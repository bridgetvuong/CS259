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
    CH:	      AgentId;
    RES:      AgentId;
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

    uehe: UEHEMessage;
    snhe: SNHEMessage;
    snue: SNUEMessage;

    -- Assume VP and Qid do not need to be passed, cryptography abstraction for IBE
  end;

  -- remark: keys, nonces and addresses are encoded in the message by their
  --         agent*s identifier only. They can be distinguished by their po-
  --         sition and the type of the message

  UEStates : enum {
    UE_IDLE,                     -- state after initialization
    UE_WAIT,                      -- waiting for response from responder
    UE_DONE                     -- initiator commits to session
  };                             --  (thinks responder is authenticated)

  UE : record
    state:     UEStates;
    sn: AgentId;          -- agent with whom the initiator starts the
    he: AgentId;
    cid: AgentId;
    aid: AgentId;
    dhs: array[1..3] of AgentId;
  end;                           --  protocol

  SNStates : enum {
    SN_IDLE,
    SN_WAIT_HE1,
    SN_WAIT_UE,
    SN_WAIT_HE2,
    SN_DONE
  };

  SN : record
    state:     SNStates;
    -- HEIDs:     array[AgentId] of AgentId;
    CIDs: array[AgentId] of AgentId;
    AIDs: array[AgentId] of AgentId;
    dhs: array[AgentId] of array[]
  end;

  HEStates : enum {
    HE_IDLE,
    HE_WAIT,
    HE_DONE
  };

  HE : record
    state:     HEStates;
    initiator: AgentId;
  end;

  Intruder : record
    nonces:   array[AgentId] of boolean;           -- known nonces
    messages: multiset[MaxKnowledge] of Message;   -- known messages
  end;
    

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
var                                         -- state variables for
  netA: multiset[NetworkSize] of Message;   --  network A-interface
  netB: multiset[NetworkSize] of Message;   --  network B-interface
  UEs: array[UEID] of UE;     	 	    --  UEs
  SNs: array[SNID] of SN;     		    --  SNs
  HEs: array[HEID] of HE;		    --  HEs
  adv: array[intruderId] of Intruder;       --  adversaries



--------------------------------------------------------------------------------
-- rules
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- behavior of initiators

-- initiator i starts protocol with responder or intruder j (step 3)
ruleset i: InitiatorId do
  ruleset j: AgentId do
    rule 20 "initiator starts protocol (step 3)"

      ini[i].state = I_SLEEP &
      !ismember(j,InitiatorId) &               -- only responders and intruders
      multisetcount (l:net, true) < NetworkSize

    ==>
    
    var
      outM: Message;   -- outgoing message

    begin
      undefine outM;
      outM.source  := i;
      outM.dest    := j;
      outM.key     := j;
      outM.mType   := M_NonceAddress;
      outM.nonce1  := i;
      outM.nonce2  := i;

      multisetadd (outM,net);

      ini[i].state     := I_WAIT;
      ini[i].responder := j;
    end;
  end;
end;

-- initiator i reacts to nonce received (steps 6/7)
ruleset i: InitiatorId do
  choose j: net do
    rule 20 "initiator reacts to nonce received (steps 6/7)"

      ini[i].state = I_WAIT &
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

        if inM.mType=M_NonceNonceAddress then   -- correct message type
          if inM.nonce1=i &                     -- correct nonce and address
             (!FIXED | inM.address=ini[i].responder) then
            undefine outM;
            outM.source  := i;
            outM.dest    := ini[i].responder;
            outM.key     := ini[i].responder;
            outM.mType   := M_Nonce;
            outM.nonce1  := inM.nonce2;

            multisetadd (outM,net);

            ini[i].state := I_COMMIT;
          else
            --error "initiator received incorrect nonce"
          end;
        end;

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
