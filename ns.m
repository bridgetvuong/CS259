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
--  * Lowe*s fix can be turned on and off
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
  UEID:  scalarset (NumUEs);   -- identifiers
  SNID:  scalarset (NumSNs);
  HEID:  scalarset (NumHEs);  
  IntruderId:   scalarset (NumIntruders);
  
  AgentId:      union { UEID, SNID, HEID, IntruderId };

  MessageType : enum {           -- different types of messages
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
    CHRES:	  symkey;
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
    source:   AgentId;           -- source of message
    dest:     AgentId;           -- intended destination of message
    mType:    MessageType;       -- type of message
    key:      symkey;              -- key used for encryption

    uehe:     UEHEMessage;
    snhe:     SNHEMessage;
    snue:     SNUEMessage;

    -- Assume VP and Qid do not need to be passed, cryptography abstraction for IBE
  end;

  -- remark: keys, nonces and addresses are encoded in the message by their
  --         agent*s identifier only. They can be distinguished by their po-
  --         sition and the type of the message

  UEStates : enum {
    UE_IDLE,                     -- state after initialization
    UE_WAIT,                     -- waiting for response from responder
    UE_DONE                      -- initiator commits to session
  };                             --  (thinks responder is authenticated)

  UE : record
    state:    UEStates;
    SN:     AgentId;          -- agent with whom the initiator starts the
    HE:     AgentId;
    dhs:      dhs;
    -- UE's CID and AID are the same as its own ID
  end;                           --  protocol

  SNStates : enum {
    SN_IDLE,
    SN_WAIT_HE1,
    SN_WAIT_UE,
    SN_WAIT_HE2,
    SN_DONE
  };

  SN : record
    state:    SNStates;
    HEs:    array[HEID] of AgentId;
    CIDs:     array[UEID] of AgentId; -- mapping from CID to AID is just equality
    dhs:      array[UEID] of dhs;
  end;

  HEStates : enum {
    HE_IDLE,
    HE_WAIT,
    HE_DONE
  };

  HE : record
    state:     HEStates;
    SNIDs:     array[SNID] of AgentId;
    UEIDs:     array[UEID] of AgentId;
    dhs:       array[UEID] of dhs;
  end;

  Intruder : record
    nonces:   array[AgentId] of boolean;           -- known nonces
    messages: multiset[MaxKnowledge] of Message;   -- known messages
  end;
    

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
var                                         -- state variables for
  net: multiset[NetworkSize] of Message;    --  network
  UEs: array[UEID] of UE;                   --  UEs
  SNs: array[SNID] of SN;                   --  SNs
  HEs: array[HEID] of HE;                   --  HEs
  adv: array[intruderId] of Intruder;       --  adversaries


function hasKey(key: symkey, entity: AgentId): boolean;
begin
    return (isundefined(key) | key.entity1 = entity | key.entity2 = entity);
end;

--------------------------------------------------------------------------------
-- rules in order of messages
--------------------------------------------------------------------------------

-- UE starts protocol with SN or intruder j (message M1)
ruleset i: UEID do
  ruleset j: AgentId do
    ruleset k: AgentId do
        rule 20 "UE starts protocol (message M1)"

          UEs[i].state = UE_IDLE &
          (ismember(j,SNID) | ismember(j,intruderId)) &               -- only responders and intruders
          (ismember(k,HEID) | ismember(k,intruderId)) &
          multisetcount (l:net, true) < NetworkSize

        ==>
        
        var
          outM: Message;   -- outgoing message

        begin
          undefine outM;
          outM.source := i;
          outM.dest := j;
          outM.mType := M1;
          outM.uehe.UEID := i;
          outM.uehe.CID := i;
          outM.uehe.CHRES.entity1 := i;
          outM.uehe.CHRES.entity2 := k;
          outM.uehe.key := k;
          outM.snue.HEID := k;

          multisetadd (outM,net);

          UEs[i].state     := UE_WAIT;
          UEs[i].SN := j;
          UEs[i].HE := k;
        end;
    end;
  end;
end;

-- SN responds to message (M1, M3, M5, or M7)
ruleset i: SNID do
  choose j: net do
    rule 20 "SN responds to message (M1, M3, M5, or M7)"

      SNs[i].state = SN_IDLE &
      net[j].dest = i &
      ismember(net[j].source,IntruderId)
    ==>

    var
      outM: Message;   -- outgoing message
      inM:  Message;   -- incoming message

    begin
      inM := net[j];
      multisetremove (j,net);

      if hasKey(inM.key, i) then   -- message is encrypted with i*s key

        switch inM.mType
        case M1: -- send M2
            undefine outM;
            outM.source := i;
            outM.dest := inM.snhe.HEID;
            outM.key.entity1 := i;
            outM.key.entity2 := inM.snhe.HEID;
            outM.mType := M2;
            outM.uehe := inM.uehe;
            outM.snhe.DH := i;
            SNs[i].state = SN_WAIT_HE1;
        case M3: -- send M4
            undefine outM;
            outM.source := i;
            outM.dest := inM.snhe.CID; -- broadcast? Question for Jason?
            outM.mType := M4;
            outM.uehe := inM.uehe;
            outM.snue.CID := inM.snhe.CID;
            outM.snue.AID := inM.snhe.CID;
            outM.snue.key.entity1 = i;
            outM.snue.key.entity2 = inM.snhe.CID; -- since in our case CID is the same as UEID
            SNs[i].state = SN_WAIT_UE;
        case M5:
        
        case M7:
        
        else:
            error "SN received random message"
        end;

        multisetadd (outM,net);

      end;
    end;
  end;
end;


--------------------------------------------------------------------------------
-- behavior of responders

-- responder i reacts to initiator*s nonce (steps 3/6)
ruleset i: ResponderId do
  choose j: net do
    rule 20 "responder reacts to initiator*s nonce (steps 3/6)"

      res[i].state = R_SLEEP &
      net[j].dest = i &
      ismember(net[j].source,IntruderId)

    ==>

    var
      outM: Message;   -- outgoing message
      inM:  Message;   -- incoming message

    begin
      inM := net[j];
      multisetremove (j,net);

      if inM.key=i then   -- message is encrypted with i*s key
        if inM.mType=M_NonceAddress then   -- correct message type
          undefine outM;
          outM.source  := i;
          outM.dest    := inM.nonce2;   -- identifier of initiator
          outM.key     := inM.nonce2;
          outM.mType   := M_NonceNonceAddress;
          outM.nonce1  := inM.nonce1;
          outM.nonce2  := i;
          outM.address := i;

          multisetadd (outM,net);

          res[i].state     := R_WAIT;
          res[i].initiator := inM.nonce2;
        end;
      end;

    end;
  end;
end;

-- responder i reacts to own nonce (step 7)
ruleset i: ResponderId do
  choose j: net do
    rule 20 "responder reacts to own nonce (step 7)"

      res[i].state = R_WAIT &
      net[j].dest = i &
      ismember(net[j].source,IntruderId)

    ==>

    begin
      alias inM: net[j] do   -- incoming message

        if inM.key=i then   -- message is encrypted with i*s key

          if inM.mType=M_Nonce then   -- correct message type
            if inM.nonce1=i then   -- correct nonce received
              res[i].state := R_COMMIT;
            else
              --error "responder received incorrect nonce"
            end;
          end;

        end;

        multisetremove (j,net);
      end;
    end;
  end;
end;


--------------------------------------------------------------------------------
-- behavior of intruders

-- intruder i intercepts messages
ruleset i: IntruderId do
  choose j: net do
      rule 10 "intruder intercepts"

        !ismember (net[j].source, IntruderId)    -- not for intruders* messages

      ==>

      var
        temp: Message;

      begin
        alias msg: net[j] do   -- message to intercept

          if msg.key=i then   -- message is encrypted with i*s key
            int[i].nonces[msg.nonce1] := true;     -- learn nonces
            if msg.mType=M_NonceNonceAddress then
              int[i].nonces[msg.nonce2] := true;
            end;
          else                                     -- learn message
            alias messages: int[i].messages do
              temp := msg;
              undefine temp.source;   -- delete useless information
              undefine temp.dest;
              if multisetcount (l:messages,   -- add only if not there
                   messages[l].key = temp.key & 
                   messages[l].mType = temp.mType &
                   messages[l].nonce1 = temp.nonce1 &
                   ( messages[l].mType != M_Nonce ->
                     messages[l].nonce2 = temp.nonce2 ) &
                   ( messages[l].mType = M_NonceNonceAddress ->
                     messages[l].address = temp.address ) ) = 0 then
                multisetadd (temp, int[i].messages);
              end;
            end;
          end;

          multisetremove (j,net);
        end;
      end;
  end;
end;

-- intruder i sends recorded message
ruleset i: IntruderId do         -- arbitrary choice of
  choose j: int[i].messages do   --  recorded message
    ruleset k: AgentId do        --  destination
      rule 90 "intruder sends recorded message"

        !ismember(k, IntruderId) &                 -- not to intruders
        multisetcount (l:net, true) < NetworkSize

      ==>

      var
        outM: Message;

      begin
        outM        := int[i].messages[j];
        outM.source := i;
        outM.dest   := k;

        multisetadd (outM,net);
      end;
    end;
  end;
end;

-- intruder i generates message with the nonces it knows
ruleset i: IntruderId do       -- arbitrary choice of
 ruleset j: AgentId do         --  destination = key
  ruleset l: MessageType do    --  message type
   ruleset m: AgentId do       --  nonce1
    ruleset n: AgentId do      --  nonce2
     ruleset o: AgentId do     --  address
      rule 90 "intruder generates message"

        !ismember(j, IntruderId) &       -- not to intruders
        int[i].nonces[m] = true &        -- nonces must be known
        int[i].nonces[n] = true &
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
      int[i].nonces[j] := false;
    end;
    int[i].nonces[i] := true;
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
