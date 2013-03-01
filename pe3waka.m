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
	NumAdvs:  1;   -- number of intruders
	MaxKnowledge:   10;   -- max. number of messages intruder can remember
	NetworkASize:   3;   -- max. number of outstanding messages in network
	NetworkBSize:	NumUEs;


-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
type

	UEID:  scalarset (NumUEs);
	SNID:  scalarset (NumSNs);
	HEID:  scalarset (NumHEs);  
	AdvId: scalarset (NumAdvs);
  
	AgentId: union { UEID, SNID, HEID, AdvId };

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
	Key : record
		entity1: AgentId;
		entity2: AgentId;
		-- if yes, both entities are used
		-- otherwise, only entity1 is used
		isSymkey : boolean;
	end;

	-- Diffie Hellman secret
	dhs : record
		UEID: AgentId;
		HEID: AgentId;
		SNID: AgentId;
	end;

	-- UE-HE exchange
	UEHEMessage : record
		UEID:	AgentId;
		CID:	AgentId;
		CHRES:	Key;
		dhs:	dhs;
		key:	Key;
	end;

	-- SN-UE exchange
	SNUEMessage : record
		HEID:	AgentId;
		AID:	AgentId;
		CID:	AgentId;
		key:	Key;
	end;

	-- SN-HE exchange
	SNHEMessage : record
		CID:	AgentId;
		DH:	AgentId;
	end;

	-- Overall message
	Message : record
		source:	AgentId;		-- source of message
		dest:	AgentId;		-- intended destination of message
		mType:	MessageType;		-- type of message
		key:	Key;		-- key used for encryption
		transactionId: UEID;	-- used to group messages within a single authentication attempt
		
		uehe:	UEHEMessage;
		snhe:	SNHEMessage;
		snue:	SNUEMessage;
		
		-- Assume VP and Qid do not need to be passed, cryptography abstraction for IBE
	end;

	UEStates : enum {
		UE_IDLE,
		UE_WAIT_M4,
		UE_DONE
	};				

	UE : record
		state:	UEStates;
		SN:	AgentId;
		HE:	AgentId;
		CHRES:	Key;
		dhs:	dhs;
		CID:	AgentId;
		AID:	AgentId;
	end;

	SNStates : enum {
		SN_IDLE,
		SN_WAIT_M3,
		SN_WAIT_M5,
		SN_WAIT_M7,
		SN_DONE
	};

	SN : record
		states:		 array[UEID] of SNStates;
		CIDs:		 array[UEID] of AgentId;
		UEIDs:		 array[UEID] of boolean;
		CIDtoHEID: 	 array[UEID] of AgentId;
		CIDtoAID:	 array[UEID] of AgentId; -- mapping from CID to AID should be equality
		dhs:		 array[UEID] of dhs;
	end;

	HEStates : enum {
		HE_IDLE,
		HE_WAIT_M6,
		HE_DONE
	};

	HE : record
		states:	array[UEID] of HEStates;
		CIDs:		 array[UEID] of AgentId;
		CHRESs:	array[UEID] of Key;
		dhs:	array[UEID] of dhs;
	end;

	Adversary : record
		UEIDs:		array[UEID] of boolean;	   -- known UEIDs
		CIDs:		array[UEID] of boolean;	   -- known CIDs
		CIDtoAIDs:	array[UEID] of boolean;	   -- known mappings between CID and AID
		dhs:		array[UEID] of boolean;	   -- known dhs indexed by UEID
		messages:	multiset[MaxKnowledge] of Message;   -- known messages
		--M4messages: multiset[MaxKnowledge] of Message;   -- known messages
		--M5messages: multiset[MaxKnowledge] of Message;   -- known messages
	end;
    

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
var    	       	       	       	       	       	 -- state variables for
	netA: multiset[NetworkASize] of Message;  --  network interface A
	netB: multiset[NetworkBSize] of Message;  --  network interface B
	UEs:  array[UEID] of UE;       		 --  UEs
	SNs:  array[SNID] of SN;		 --  SNs
	HEs:  array[HEID] of HE;		 --  HEs
	adv:  array[AdvId] of Adversary;	 --  adversaries


-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
function hasKey(key: Key; entity: AgentId): boolean;
begin
	if (isundefined(key.isSymkey)) then return true; end;

	if (key.isSymkey) then
		return (key.entity1 = entity | key.entity2 = entity);
	else
		return (key.entity1 = entity);
	end;
end;

function keysAreEqual(key1, key2: Key): boolean;
begin
	if (isundefined(key1.isSymkey) & isundefined(key2.isSymkey)) then return true; end;
	if (key1.isSymkey != key2.isSymkey) then return false; end;

	if (key1.isSymkey) then
		return ((key1.entity1 = key2.entity1 & key1.entity2 = key2.entity2) | 
				(key1.entity1 = key2.entity2 & key1.entity2 = key2.entity1));
	else
		return (key1.entity1 = key2.entity1);
	end;
end;

function dhsAreEqual(dhs1, dhs2: dhs): boolean;
begin
	return (dhs1.UEID = dhs2.UEID & dhs1.SNID = dhs2.SNID & dhs1.HEID = dhs2.HEID);
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
		(ismember(j,SNID) | ismember(j,AdvId)) & -- only responders and intruders
		multisetcount (l:netA, true) < NetworkASize

		==>
    
		var
			outM: Message;

		begin
			undefine outM;
			outM.source := i;
			outM.dest := j;
			outM.mType := M1;
			outM.transactionId := i;
			outM.uehe.UEID := i;
			outM.uehe.CID := i;
			outM.uehe.CHRES.entity1 := i;
			outM.uehe.CHRES.entity2 := UEs[i].HE;
			outM.uehe.CHRES.isSymkey := true;
			outM.uehe.key.entity1 := UEs[i].HE;
			outM.uehe.key.isSymkey := false;
			outM.snue.HEID := UEs[i].HE;

			multisetadd (outM,netA);

			UEs[i].state := UE_WAIT_M4;
			UEs[i].CID := i;
			UEs[i].CHRES := outM.uehe.CHRES;
		end;
	end;
end;

-- UE responds to message M4
ruleset i: UEID do
	choose j: netA do
		alias inM: netA[j] do
			rule 20 "UE responds to message M4"

			UEs[i].state = UE_WAIT_M4 &			-- UE expecting message M4
			inM.dest = i &
			ismember(inM.source,AdvId) &	-- only from intruder
			inM.mType = M4 &		      	-- message type is M4
			hasKey(inM.key, i) &		-- UE can decrypt message

			hasKey(inM.uehe.key, i) & 		-- UE can decrypte message from HE
			hasKey(inM.uehe.CHRES, i) &		-- CH/RES between UE and HEu is valid 
			hasKey(inM.snue.key, i) & 		-- can decrypt with mtk
			inM.uehe.CID = UEs[i].CID & inM.snue.CID = UEs[i].CID	-- CID from HE and SN agree

			==>
    
			var
				outM: Message;

			begin
				undefine outM;
				outM.source := i;
				outM.dest := UEs[i].SN;
				outM.key := inM.snue.key;
				outM.mType := M5;
				outM.transactionId := inM.transactionId;
				outM.uehe.CID := UEs[i].CID;
				outM.uehe.CHRES := inM.uehe.CHRES;
				outM.uehe.key := inM.uehe.key;
				outM.snue.AID := inM.snue.AID;

				UEs[i].state := UE_DONE;
				UEs[i].dhs := inM.uehe.dhs;
				UEs[i].AID := inM.snue.AID;

				multisetremove (j,netA);
				multisetadd (outM,netA);
			end;
		end;
	end;
end;


--------------------------------------------------------------------------------
-- behavior of SNs

ruleset i: SNID do
	choose j: netA do
		alias inM: netA[j] do
			rule 20 "SN responds to message M1"

			SNs[i].states[inM.transactionId] = SN_IDLE &
			inM.dest = i &
			ismember(inM.source,AdvId) &
			inM.mType = M1 &
			hasKey(inM.key, i)

			==>

			var
				outM: Message;

			begin
				undefine outM;
				outM.source := i;
				outM.dest := inM.snue.HEID;
				outM.key.entity1 := i;
				outM.key.entity2 := inM.snue.HEID;
				outM.key.isSymkey := true;
				outM.mType := M2;
				outM.transactionId := inM.transactionId;
				outM.uehe := inM.uehe;
				outM.snhe.DH := i;

				SNs[i].states[inM.transactionId] := SN_WAIT_M3;
				if hasKey(inM.uehe.key, i) then
					SNs[i].UEIDs[inM.uehe.UEID] := true;
				end;

				multisetremove (j,netA);
				multisetadd (outM,netB);
			end;


			rule 20 "SN responds to message M5"

			SNs[i].states[inM.transactionId] = SN_WAIT_M5 &
			inM.dest = i &
			ismember(inM.source,AdvId) &
			inM.mType = M5 &
			hasKey(inM.key, i)

			==>

			var
				outM: Message;
				CID:	AgentId;

			begin				
				if inM.key.entity1 = i then
					CID := inM.key.entity2;
				else
					CID := inM.key.entity1;
				end;

				if SNs[i].CIDtoAID[CID] = inM.snue.AID then
					undefine outM;
					outM.source := i;
					outM.dest := SNs[i].CIDtoHEID[CID];
					outM.key.entity1 := i;
					outM.key.entity2 := SNs[i].CIDtoHEID[CID];
					outM.key.isSymkey := true;
					outM.mType := M6;
					outM.transactionId := inM.transactionId;
					outM.uehe := inM.uehe;
					outM.snhe.CID := CID;

					multisetadd (outM,netB);

					SNs[i].states[inM.transactionId] := SN_WAIT_M7;
				end;

				multisetremove (j,netA);
			end;
		end;
	end;
end;

ruleset i: SNID do
	choose j: netB do
		alias inM: netB[j] do
			rule 20 "SN responds to message M3"

			SNs[i].states[inM.transactionId] = SN_WAIT_M3 &
			inM.dest = i &
			ismember(inM.source,HEID) &
			inM.mType = M3 &
			hasKey(inM.key, i)

			==>

			var
				outM: Message;

			begin

				undefine outM;
				outM.source := i;
				outM.dest := inM.snhe.CID; -- broadcast but just for state space constraints
				outM.mType := M4;
				outM.transactionId := inM.transactionId;
				outM.uehe := inM.uehe;
				outM.snue.CID := inM.snhe.CID;
				outM.snue.AID := inM.snhe.CID;
				outM.snue.key.entity1 := i;
				outM.snue.key.entity2 := inM.snhe.CID; -- since in our case CID is the same as UEID
				outM.snue.key.isSymkey := true;

				SNs[i].states[inM.transactionId] := SN_WAIT_M5;
				SNs[i].CIDtoHEID[inM.snhe.CID] := inM.source;
				SNs[i].CIDtoAID[inM.snhe.CID] := outM.snue.AID;
				SNs[i].dhs[inM.snhe.CID].UEID := inM.snhe.CID;
				SNs[i].dhs[inM.snhe.CID].SNID := i;
				SNs[i].dhs[inM.snhe.CID].HEID := inM.snhe.DH;

				multisetremove (j,netB);
				multisetadd (outM,netA);
			end;


			rule 20 "SN responds to message M7"

			SNs[i].states[inM.transactionId] = SN_WAIT_M7 &
			inM.dest = i &
			ismember(inM.source,HEID) &
			inM.mType = M7 &
			hasKey(inM.key, i) &

			SNs[i].CIDtoHEID[inM.snhe.CID] = inM.source

			==>

			begin
				SNs[i].CIDs[inM.transactionId] := inM.snhe.CID;
				SNs[i].states[inM.transactionId] := SN_DONE;
			end;
		end;
	end;
end;


--------------------------------------------------------------------------------
-- behavior of HEs

ruleset i: HEID do
	choose j: netB do
		alias inM: netB[j] do
			rule 20 "HE responds to message M2"

			HEs[i].states[inM.transactionId] = HE_IDLE &
			inM.dest = i &
			ismember(inM.source,SNID) &
			inM.mType = M2 &
			hasKey(inM.key, i) &
			hasKey(inM.uehe.key, i) &
			hasKey(inM.uehe.CHRES, i)

			==>

			var
				outM: Message;   -- outgoing message

			begin
				undefine outM;
				outM.source := i;
				outM.dest := inM.source;
				outM.key := inM.key;
				outM.mType := M3;
				outM.transactionId := inM.transactionId;
				outM.uehe.CID := inM.uehe.CID;
				outM.uehe.CHRES := inM.uehe.CHRES;
				outM.uehe.dhs.UEID := inM.uehe.UEID;
				outM.uehe.dhs.HEID := i;
				outM.uehe.dhs.SNID := inM.snhe.DH;
				outM.uehe.key.entity1 := inM.uehe.UEID;
				outM.uehe.key.entity2 := i;
				outM.uehe.key.isSymkey := true;
				outM.snhe.DH := i;
				outM.snhe.CID := inM.uehe.CID;

				HEs[i].states[inM.transactionId] := HE_WAIT_M6;
				HEs[i].CIDs[inM.uehe.UEID] := inM.uehe.CID;
				HEs[i].dhs[inM.uehe.UEID] := outM.uehe.dhs;

				multisetremove (j,netB);
				multisetadd (outM,netB);					
			end;


			rule 20 "HE responds to message M6"

			HEs[i].states[inM.transactionId] = HE_WAIT_M6 &
			inM.dest = i &
			ismember(inM.source,SNID) &
			inM.mType = M6 &
			hasKey(inM.key, i) &

			hasKey(inM.uehe.key, i) &
			hasKey(inM.uehe.CHRES, i) &
			inM.uehe.CID = inM.snhe.CID

			==>

			var
				outM: Message;   -- outgoing message

			begin
				undefine outM;
				outM.source := i;
				outM.dest := inM.source;
				outM.mType := M7;
				outM.transactionId := inM.transactionId;
				outM.snhe.CID := inM.snhe.CID;

				HEs[i].states[inM.transactionId] := HE_DONE;
				HEs[i].CHRESs[inM.uehe.CID] := inM.uehe.CHRES;

				multisetremove (j,netB);
				multisetadd (outM,netB);					
			end;
		end;
	end;
end;


--------------------------------------------------------------------------------
-- behavior of intruders

-- intruder i intercepts messages
ruleset i: AdvId do
	choose j: netA do
		alias inM: netA[j] do
			rule 10 "intruder intercepts"

			!ismember (inM.source, AdvId)    -- not for intruders* messages

			==>

			var
				temp: Message;

			begin
				temp := inM;

				switch inM.mType
					case M1:
						if hasKey(inM.key, i) & hasKey(inM.uehe.key, i) then
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
				end;

				multisetremove (j,netA);
				multisetadd (temp, adv[i].messages);
			end;
		end;
	end;
end;

-- intruder i generates message
ruleset i: AdvId do
	ruleset j: AgentId do
		ruleset k: MessageType do
			choose l: adv[i].messages do
				choose m: adv[i].messages do
					alias messages: adv[i].messages do
						rule 90 "intruder generates message (recorded or frankenstein)"

						((ismember(j, UEID) & k = M4) | 
						(ismember(j, SNID) & (k = M1 | k = M5))) &
						messages[l].mType = k & messages[m].mType = k &
						multisetcount (t:netA, true) < NetworkASize
					
						==>

						var
							outM: Message;
						
						begin
							undefine outM;

							-- If you can decrypt both message l and m, proceed with
							-- frankenstein-ing. Otherwise just send message m.
							if (hasKey(messages[l].key, i) |
								(messages[l].mType = M5 & adv[i].dhs[messages[l].source]))	&
								(hasKey(messages[m].key, i) |
								(messages[m].mType = M5 &	adv[i].dhs[messages[m].source])) then
								outM.uehe := messages[l].uehe;
								outM.snue := messages[m].snue;
								outM.transactionId := messages[l].transactionId;
							else
								outM := messages[m];
							end;

							outM.source := i;
							outM.dest   := j;
							outM.mType  := k;
							multisetadd (outM,netA);
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
startstate
	-- initialize UEs
	undefine UEs;
	-- TODO: make SN, HE assignment many-to-one
	for i: UEID do
	    UEs[i].state := UE_IDLE;
	    for s : SNID do
		    UEs[i].SN := s;
			for h : HEID do
			    UEs[i].HE := h;
		    end;
		end;
	end;

	-- initialize SNs
	undefine SNs;
	for i: SNID do
		for j: UEID do
			SNs[i].states[j] := SN_IDLE;
			SNs[i].UEIDs[j] := false;
		end;
	end;

	-- initialize HEs
	undefine HEs;
	for i: HEID do
		for j : UEID do
			HEs[i].states[j] := HE_IDLE;
		end;
	end;

	-- initialize intruders
	undefine adv;
	for i: AdvId do
		for j: UEID do  
			adv[i].UEIDs[j] := false;
			adv[i].CIDs[j] := false;
			adv[i].CIDtoAIDs[j] := false;
			adv[i].dhs[j] := false;
		end;
	end;

	-- initialize network 
	undefine netA;
	undefine netB;
end;


--------------------------------------------------------------------------------
-- invariants
--------------------------------------------------------------------------------

invariant "adversary does not learn identity of UE"
	forall i: AdvId do
		forall j: UEID do

			UEs[j].state = UE_DONE
			->
			(!adv[i].UEIDs[j] & !adv[i].CIDs[j])
		end
	end;

invariant "adversary does not learn location of UE"
	forall i: AdvId do
		forall j: UEID do

			UEs[j].state = UE_DONE
			->
			!adv[i].CIDtoAIDs[j]
		end
	end;

invariant "SN does not learn identity of UE"
	forall i: SNID do
		forall j: UEID do

			SNs[i].states[j] = SN_DONE &
			UEs[j].state = UE_DONE
			->
			!SNs[i].UEIDs[j]
		end
	end;

invariant "SN and UE agree on AID"
	forall i: SNID do
		forall j: UEID do

			SNs[i].states[j] = SN_DONE &
			UEs[j].state = UE_DONE
			->
			SNs[i].CIDtoAID[j] = UEs[j].AID
		end
	end;

invariant "HE and UE are mutually authenticated"
	forall i: HEID do
		forall j: UEID do

			HEs[i].states[j] = HE_DONE &
			UEs[j].state = UE_DONE
			->
			keysAreEqual(HEs[i].CHRESs[j], UEs[j].CHRES)
		end
	end;

invariant "HE, SN, and UE agree that protocol has ended"
	forall i: UEID do
		SNs[UEs[i].SN].states[i] = SN_DONE
		->
		HEs[UEs[i].HE].states[i] = HE_DONE &
		UEs[i].state = UE_DONE
	end;

invariant "HE, SN, and UE agree on dhs"
	forall i: HEID do
		forall j: SNID do
			forall k: UEID do

				HEs[i].states[k] = HE_DONE &
				SNs[j].states[k] = SN_DONE &
				UEs[k].state = UE_DONE
				->
				dhsAreEqual(UEs[k].dhs, SNs[j].dhs[k]) &
				dhsAreEqual(UEs[k].dhs, HEs[i].dhs[k])
			end
		end
invariant "HE, SN, and UE agree on CID"
	forall i: UEID do
		HEs[UEs[i].HE].states[i] = HE_DONE &
		SNs[UEs[i].SN].states[i] = SN_DONE &
		UEs[i].state = UE_DONE
		->
		UEs[i].CID = SNs[UEs[i].SN].CIDs[i] &
		UEs[i].CID = HEs[UEs[i].HE].CIDs[i]
	end;
