--------------------------------------------------------------------------------
--
--  Murphi Model of the Needham-Schroeder protocol
--
--------------------------------------------------------------------------------
--
--  version:      1.0
--
--  written by:   Ulrich Stern
--  date:         Aug 1998
--  affiliation:  Stanford University (research associate)
--
--------------------------------------------------------------------------------
--
--  only the following three steps of the protocol are modeled:
--
--   3. A->B: {Na,A}Kb
--   6. B->A: {Na,Nb,B}Ka       -- A assumes it is talking to B
--   7. A->B: {Nb}Kb            -- B assumes it is talking to A
--
--   A: initiator, B: reponder
--
--------------------------------------------------------------------------------

--
--  this version has the following improvements:
--  * intruder always intercepts, agents only react to intruder
--


--------------------------------------------------------------------------------
-- constants, types and variables
--------------------------------------------------------------------------------


-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
const

  NumUEs:   1;   -- number of user entities
  NumSNs:   1;   -- number of serving networks
  NumHEs:   1;   -- number of home environments
  NumIntruders:    1;   -- number of intruders
  NetworkSize:     1;   -- max. number of outstanding messages in network
  MaxKnowledge:   10;   -- max. number of messages intruder can remember


-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
type

  UEID:  scalarset (NumUEs);
  SNID:  scalarset (NumSNs);
  HEID:  scalarset (NumHEs);  
  IntruderId:   scalarset (NumIntruders);
  
  AgentId:      union { UEID, SNID, HEID, IntruderId };

  MessageType : enum {
    M1,
    M2,
    M3,
    M4,
    M5,
    M6,
    M7
  };

  -- Symmetric key between two entities
  symkey : record
    entity1:     AgentId;
    entity2:     AgentId;
  end;

  -- Diffie Hellman secret
  dhs : record
    UEID: AgentId;
    HEID: AgentId;
    SNID: AgentId;
  end;

  -- UE-HE exchange
  UEHEMessage : record
    UEID:     AgentId;
    CID:      AgentId;
    CHRES:    symkey;
    dhs:      dhs;
    key:      union { AgentId, symkey };
  end;

  -- SN-UE exchange
  SNUEMessage : record
    HEID:     AgentId;
    AID:      AgentId;
    CID:      AgentId;
    key:      symkey;
  end;

  -- SN-HE exchange
  SNHEMessage : record
    CID:      AgentId;
    DH:       AgentId;
  end;

  -- Overall message
  Message : record
    source:   AgentId;					 -- source of message
    dest:     AgentId;					 -- intended destination of message
    mType:    MessageType;			 -- type of message
    key:      symkey;						 -- key used for encryption

    uehe:     UEHEMessage;
    snhe:     SNHEMessage;
    snue:     SNUEMessage;

    -- Assume VP and Qid do not need to be passed, cryptography abstraction for IBE
  end;

  UEStates : enum {
    UE_IDLE,										-- state after initialization
    UE_WAIT_M4,									-- waiting for response from responder
    UE_DONE											-- initiator commits to session
  };														--  (thinks responder is authenticated)

  UE : record
    state:    UEStates;
    SN:     AgentId;
    HE:     AgentId;
    dhs:    dhs;
    -- UE*s CID and AID are the same as its own ID
  end;

  SNStates : enum {
    SN_IDLE,
    SN_WAIT_M3,
    SN_WAIT_M5,
    SN_WAIT_M7,
    SN_DONE
  };

  SN : record
    state:    SNStates;
    CIDtoHEID:     array[UEID] of AgentId; -- mapping from CID to AID is just equality
    dhs:      array[UEID] of dhs; -- TODO: store in messages
  end;

  HEStates : enum {
    HE_IDLE,
    HE_WAIT_M6,
    HE_DONE
  };

  HE : record
    state:     HEStates;
    SNIDs:     array[SNID] of AgentId;
    UEIDs:     array[UEID] of AgentId;
    dhs:       array[UEID] of dhs; -- TODO: store in messages
  end;

  Intruder : record
    UEIDs:     array[UEID] of boolean;	   -- known UEIDs
    CIDs:      array[UEID] of boolean;	   -- known CIDs
    CIDtoAIDs: array[UEID] of boolean;	   -- known mappings between CID and AID
    dhs:       array[UEID] of boolean;	   -- known dhs indexed by UEID
    messages: multiset[MaxKnowledge] of Message;   -- known messages
  end;
    

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
var                                        -- state variables for
  netA: multiset[NetworkSize] of Message;  --  network interface A
  netB: multiset[NetworkSize] of Message;  --  network interface B
  UEs: array[UEID] of UE;                  --  UEs
  SNs: array[SNID] of SN;                  --  SNs
  HEs: array[HEID] of HE;                  --  HEs
  adv: array[intruderId] of Intruder;      --  adversaries


-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
function hasKey(key: symkey, entity: AgentId): boolean;
begin
  return (isundefined(key) | key.entity1 = entity | key.entity2 = entity);
end;

--------------------------------------------------------------------------------
-- rules
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- behavior of UEs

-- UE starts protocol with SN or intruder j (message M1)
ruleset i: UEID do
  ruleset j: AgentId do
		rule 20 "UE starts protocol (message M1)"

			UEs[i].state = UE_IDLE &
			(ismember(j,SNID) | ismember(j,intruderId)) & -- only responders and intruders
			multisetcount (l:netA, true) < NetworkSize

			==>
        
			var
				outM: Message;

			begin
				undefine outM;
				outM.source := i;
				outM.dest := j;
				outM.mType := M1;
				outM.uehe.UEID := i;
				outM.uehe.CID := i;
				outM.uehe.CHRES.entity1 := i;
				outM.uehe.CHRES.entity2 := UEs[i].HE;
				outM.uehe.key := UEs[i].HE;
				outM.snue.HEID := UEs[i].HE;

				multisetadd (outM,netA);

				UEs[i].state := UE_WAIT_M4;
				UEs[i].SN := j;
				UEs[i].HE := UEs[i].HE;
			end;
		end;
	end;
end;

-- UE responds to message M4
ruleset i: UEID do
  choose j: netA do
    rule 20 "UE responds to message M4"
      alias inM: netA[j] do

				UEs[i].state = UE_WAIT_M4 &			-- UE expecting message M4
				inM.dest = i &
				ismember(inM.source,IntruderId) &	-- only from intruder
				inM.mtype = M4 &		      	-- message type is M4
				hasKey(inM.key, i) &		-- UE can decrypt message

				hasKey(inM.uehe.key, i) & 		-- UE can decrypte message from HE
				hasKey(inM.uehe.CHRES, i) &		-- CH/RES between UE and HEu is valid 
				hasKey(inM.snue.key, i) & 		-- can decrypt with mtk
				inM.uehe.CID = i & inM.snue.CID = i	-- CID from HE and SN agree

				==>
        
				var
					outM: Message;

				begin
					multisetremove (j,netA);

					undefine outM;
					outM.source := i;
					outM.dest := UEs[i].SN;
					outM.key = inM.snue.key;
					outM.mType := M5;
					outM.uehe.CID := i;
					outM.uehe.CHRES = inM.uehe.CHRES;
					outM.uehe.key := inM.uehe.key;
					outM.snue.AID := inM.snue.AID;

					multisetadd (outM,netA);

					UEs[i].state := UE_DONE;
					UEs[i].dhs := inM.uehe.dhs;
				end;
			end;
		end;
	end;
end;


--------------------------------------------------------------------------------
-- behavior of SNs

-- SN responds to message M1
ruleset i: SNID do
  choose j: netA do
    rule 20 "SN responds to message M1"
			alias inM: netA[j] do

				SNs[i].state = SN_IDLE &
				inM.dest = i &
				ismember(inM.source,IntruderId) &
				inM.type = M1 &
				hasKey(inM.key, i)

				==>

				var
					outM: Message;

				begin
					multisetremove (j,netA);

					undefine outM;
					outM.source := i;
					outM.dest := inM.snue.HEID;
					outM.key.entity1 := i;
					outM.key.entity2 := inM.snue.HEID;
					outM.mType := M2;
					outM.uehe := inM.uehe;
					outM.snhe.DH := i;

					multisetadd (outM,netB);

					SNs[i].state = SN_WAIT_M3;
				end;
			end;
		end;
	end;
end;

-- SN responds to message M3
ruleset i: SNID do
  choose j: netB do
    rule 20 "SN responds to message M3"
			alias inM: netB[j] do

				SNs[i].state = SN_WAIT_M3 &
				inM.dest = i &
				ismember(inM.source,IntruderId) &
				inM.type = M3 &
				hasKey(inM.key, i)

				==>

				var
					outM: Message;

				begin
					multisetremove (j,netB);

					undefine outM;
					outM.source := i;
					outM.dest := inM.snhe.CID; -- broadcast but just for state space constraints
					outM.mType := M4;
					outM.uehe := inM.uehe;
					outM.snue.CID := inM.snhe.CID;
					outM.snue.AID := inM.snhe.CID;
					outM.snue.key.entity1 = i;
					outM.snue.key.entity2 = inM.snhe.CID; -- since in our case CID is the same as UEID

					multisetadd (outM,netA);

					SNs[i].state = SN_WAIT_M5;
					SNs[i].CIDtoHEID[inM.snhe.CID] = inM.source;
				end;
			end;
		end;
	end;
end;

-- SN responds to message M5 TODO: CHECK CID to AID MAPPING?
ruleset i: SNID do
  choose j: netA do
    rule 20 "SN responds to message M5"
			alias inM: netA[j] do

				SNs[i].state = SN_WAIT_M5 &
				inM.dest = i &
				ismember(inM.source,IntruderId) &
				inM.type = M5 &
				hasKey(inM.key, i)

				==>

				var
					outM: Message;

				begin
					multisetremove (j,netA);

					undefine outM;
					outM.source := i;
					outM.dest := SNs[i].CIDtoHEID[inM.snue.AID];
					outM.key.entity1 := i;
					outM.key.entity2 := SNs[i].CIDtoHEID[inM.snue.AID];
					outM.mType := M6;
					outM.uehe := inM.uehe;
					outM.snhe.CID := inM.snhe.AID;

					multisetadd (outM,netB);

					SNs[i].state = SN_WAIT_M7;
				end;
			end;
		end;
	end;
end;

-- SN responds to message M7
ruleset i: SNID do
  choose j: netB do
    rule 20 "SN responds to message M7"
			alias inM: netB[j] do

				SNs[i].state = SN_WAIT_M7 &
				inM.dest = i &
				ismember(inM.source,IntruderId) &
				inM.type = M7 &
				hasKey(inM.key, i) &

				SNs[i].CIDtoHEID[inM.snhe.CID] = inM.source

				==>

				begin
					SNs[i].state = SN_DONE;
				end;
			end;
		end;
	end;
end;


--------------------------------------------------------------------------------
-- behavior of HEs

-- HE responds to message M2
ruleset i: HEID do
  choose j: netB do
    rule 20 "HE responds to message M2"
			alias inM: netB[j] do

				HEs[i].state = HE_IDLE &
				inM.dest = i &
				ismember(inM.source,IntruderId) &
				inM.mType = M2 &
				hasKey(inM.key, k) &

				inM.uehe.key = i &
				hasKey(inM.uehe.CHRES, i)

				==>

				var
					outM: Message;   -- outgoing message

				begin
					multisetremove (j,netB);

					undefine outM;
					outM.source := i;
					outM.dest := inM.source;
					outM.key = inM.key;
					outM.mType := M3;
					outM.uehe.CID := inM.uehe.CID;
					outM.uehe.CHRES := inM.uehe.CHRES;
					outM.uehe.dhs.UEID := inM.uehe.UEID;
					outM.uehe.dhs.HEID := i;
					outM.uehe.dhs.SNID := inM.source;
					outM.uehe.key.entity1 := inM.uehe.UEID;
					outM.uehe.key.entity2 := i;
					outM.snhe.DH := i;

					multisetadd (outM,netB);					

					HEs[i].state = HE_WAIT_M6;
				end;
			end;
		end;
	end;
end;

-- HE responds to message M6
ruleset i: HEID do
  choose j: netB do
    rule 20 "HE responds to message M6"
			alias inM: netB[j] do

				HEs[i].state = HE_WAIT_M6 &
				inM.dest = i &
				ismember(inM.source,IntruderId) &
				inM.mType = M6 &
				hasKey(inM.key, k) &

				hasKey(inM.uehe.key, i) &
				hasKey(inM.uehe.CHRES, i) &
				inM.uehe.CID = inM.snhe.CID

				==>

				var
					outM: Message;   -- outgoing message

				begin
					multisetremove (j,netB);

					undefine outM;
					outM.source := i;
					outM.dest := inM.source;
					outM.mType := M7;
					outM.snhe.CID = inM.snhe.CID;

					multisetadd (outM,netB);					

					HEs[i].state = HE_DONE;
				end;
			end;
		end;
	end;
end;


--------------------------------------------------------------------------------
-- behavior of intruders

-- intruder i intercepts messages
ruleset i: IntruderId do
  choose j: netA do
		rule 10 "intruder intercepts"
			alias inM: netA[j] do

				!ismember (inM.source, IntruderId) &    -- not for intruders* messages

				==>

				var
					temp: Message;

				begin

					switch inM.mType
						case M1:
							if hasKey(inM.key, i) & inM.uehe.key = i then
								adv[i].UEIDs[inM.uehe.UEID] := true;
								adv[i].CIDs[inM.uehe.CID] := true;
							end;
						case M4:
							if hasKey(inM.key, i) & (hasKey(inM.snue.key, i) | adv[i].dhs[inM.dest]) then
								adv[i].CIDs[inM.snue.CID] := true;
								adv[i].CIDtoAIDs[inM.snue.CID] := true;
							end;
							if hasKey(inM.uehe.key, i) then
								adv[i].CIDs[inM.uehe.CID] := true;
								adv[i].dhs[inM.uehe.dhs.UEID] := true;
							end;
						case M5:
								if (hasKey(inM.key, i) | adv[i].dhs[inM.source]) &
									hasKey(inM.uehe.key, i) then
									adv[i].CIDs[inM.uehe.CID] := true;
									adv[i].CIDtoAIDs[inM.snhe.CID] := true;
								end;	    
          else                                     -- learn message
            alias messages: adv[i].messages do
              temp := inM;
              undefine temp.source;   -- delete useless information
              undefine temp.dest;
              if multisetcount (l:messages,   -- add only if not there
                   messages[l].key = temp.key & 
                   messages[l].mType = temp.mType) then  --&
                   -- messages[l].nonce1 = temp.nonce1 &
                   --( messages[l].mType != M_Nonce ->
                   --  messages[l].nonce2 = temp.nonce2 ) &
                   --( messages[l].mType = M_NonceNonceAddress ->
                   --  messages[l].address = temp.address ) ) = 0 then
                multisetadd (temp, adv[i].messages);
              end;
            end;
          end;

          multisetremove (j,netA);
        end;
      end;
		end;
  end;
end;

function isAppropriateRecipient(k: AgentId, msg: Message): boolean;
begin
	return ((ismember(k, SNID) &
				 	(msg.mType = M1 | msg.mType = M3 | msg.mType = M5 | msg.mType = M7)) |
    	    (ismember(k, UEID) & msg.mType = M4) |
					(ismember(k, HEID) & (msg.mType = M2 | msg.mType = M6)));
end;

-- intruder i sends recorded message
ruleset i: IntruderId do         -- arbitrary choice of
  choose j: adv[i].messages do   --  recorded message
    ruleset k: AgentId do        --  destination
      rule 90 "intruder sends recorded message"

				!ismember(k, IntruderId) &                 -- not to intruders
				multisetcount (l:net, true) < NetworkSize &
				isAppropriateRecipient(k, adv[i].messages[j])

				==>

				var
					outM: Message;

				begin
					outM := adv[i].messages[j];
					outM.source := i;
					outM.dest := k;

					multisetadd (outM,netA);
      end;
    end;
  end;
end;

-- intruder i generates message with the nonces it knows
ruleset i: IntruderId do       -- arbitrary choice of
 ruleset j: AgentId do         --  destination = key
  ruleset l: MessageType do    --  message type
   ruleset m: AgentId do       --  CID
    ruleset n: AgentId do      --  nonce2
      rule 90 "intruder generates message"

        !ismember(j, IntruderId) &       -- not to intruders
        adv[i].nonces[m] = true &        -- nonces must be known
        adv[i].nonces[n] = true &
        multisetcount (t:net, true) < NetworkSize

      ==>

      var
        outM: Message;

      begin
        undefine outM;
        outM.source := i;
        outM.dest   := j;
        outM.key    := j;
        outM.mType  := l;

        switch l   -- set content dependent on message type
        case M_NonceAddress:
          outM.nonce1 := m;
          outM.nonce2 := o;
        case M_NonceNonceAddress:
          outM.nonce1  := m;
          outM.nonce2  := n;
          outM.address := o;
        case M_Nonce:
          outM.nonce1 := m;
        end;

        multisetadd (outM,net);
      end;
     end;
    end;
   end;
  end;
 end;
end;          


--------------------------------------------------------------------------------
-- startstate
--------------------------------------------------------------------------------
--TODO: initialize HEs in the UEs
startstate
  -- initialize initiators
  undefine ini;
  for i: InitiatorId do
    ini[i].state     := I_SLEEP;
    ini[i].responder := i;
  end;

  -- initialize responders
  undefine res;
  for i: ResponderId do
    res[i].state     := R_SLEEP;
    res[i].initiator := i;
  end;

  -- initialize intruders
  undefine int;
  for i: IntruderId do   -- the only nonce known is the own one
    for j: AgentId do  
      adv[i].nonces[j] := false;
    end;
    adv[i].nonces[i] := true;
  end;

  -- initialize network 
  undefine net;
end;


--------------------------------------------------------------------------------
-- invariants
--------------------------------------------------------------------------------

invariant "responder correctly authenticated"
  forall i: InitiatorId do
    ini[i].state = I_COMMIT &
    ismember(ini[i].responder, ResponderId)
    ->
    res[ini[i].responder].initiator = i &
    ( res[ini[i].responder].state = R_WAIT |
      res[ini[i].responder].state = R_COMMIT )
  end;

invariant "initiator correctly authenticated"
  forall i: ResponderId do
    res[i].state = R_COMMIT &
    ismember(res[i].initiator, InitiatorId)
    ->
    ini[res[i].initiator].responder = i &
    ini[res[i].initiator].state = I_COMMIT
  end;
