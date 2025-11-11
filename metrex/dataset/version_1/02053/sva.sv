// SVA for opc6cpu
// Bind this module to the DUT: bind opc6cpu opc6cpu_sva svai();

module opc6cpu_sva;
  // Constants (mirror DUT params for readability)
  localparam MOV=5'h0,AND_=5'h1,OR_=5'h2,XOR_=5'h3,ADD=5'h4,ADC=5'h5,STO=5'h6,LD=5'h7,ROR=5'h8,JSR=5'h9,SUB=5'hA,SBC=5'hB,INC=5'hC,LSR=5'hD,DEC=5'hE,ASR=5'hF;
  localparam HLT=5'h10,BSWP=5'h11,PPSR=5'h12,GPSR=5'h13,RTI=5'h14,NOT=5'h15,OUT=5'h16,IN=5'h17,PUSH=5'h18,POP=5'h19,CMP=5'h1A,CMPC=5'h1B;    
  localparam FET0=3'h0,FET1=3'h1,EAD=3'h2,RDM=3'h3,EXEC=3'h4,WRM=3'h5,INT=3'h6;
  localparam EI=3, IRLEN=12, IRLD=16, IRSTO=17, IRNPRED=18, IRWBK=19;
  localparam [15:0] INT_VECTOR0=16'h0002, INT_VECTOR1=16'h0004;

  // Bring DUT scope
  wire        clk, reset_b, clken;
  wire [15:0] din, dout, address;
  wire        vpa, vda, vio, rnw;
  // Internal DUT signals (hierarchical references allowed in bind)
  wire [2:0]  FSM_q; 
  wire [19:0] IR_q;
  wire [15:0] PC_q, PCI_q, OR_q;
  wire [3:0]  PSRI_q;
  wire [7:0]  PSR_q;
  wire        reset_s1_b, reset_s0_b, pred_q;
  wire [1:0]  int_b;
  wire [4:0]  op, op_d;
  wire        pred_d, pred_din;
  wire [15:0] RF_w_p2, RF_dout, operand;
  wire [15:0] result;
  wire        zero, carry, sign;
  wire [3:0]  swiid;
  wire        enable_int;

  // Hook up hierarchical signals
  bind_target bt(); // empty instance to access scope

  default clocking cb @(posedge clk); endclocking

  // Basic invariants
  // legal-state check
  assert property (FSM_q inside {FET0,FET1,EAD,RDM,EXEC,WRM,INT});

  // Reset pipeline effects (no disable)
  assert property (!reset_s1_b |-> (PC_q==16'h0 && PCI_q==16'h0 && PSRI_q==4'h0 && PSR_q==8'h0 && FSM_q==FET0));

  // clken holds registered state
  assert property (!clken |-> $stable({FSM_q,PC_q,PCI_q,PSRI_q,PSR_q,IR_q,OR_q,pred_q,reset_s0_b,reset_s1_b}));

  // Bus/control outputs
  assert property (rnw == !(FSM_q==WRM));

  assert property (dout == RF_w_p2);

  // Address mux
  assert property (((FSM_q==WRM)||(FSM_q==RDM)) |-> (address == ((op==POP)? RF_dout : OR_q)));
  assert property (!((FSM_q==WRM)||(FSM_q==RDM)) |-> (address == PC_q));

  // vpa/vda/vio protocol
  assert property (vpa == ((FSM_q==FET0)||(FSM_q==FET1)||(FSM_q==EXEC)));

  // When in RDM/WRM: exactly one of vda/vio asserted according to IN/OUT; else both 0
  assert property (((FSM_q==RDM)||(FSM_q==WRM)) |-> ({vda,vio} == {!(op==IN||op==OUT),(op==IN||op==OUT)}));
  assert property (!((FSM_q==RDM)||(FSM_q==WRM)) |-> ({vda,vio} == 2'b00));

  // IR capture (low 16b always from din in FET0/EXEC)
  assert property ($past(clken) && ($past(FSM_q)==FET0 || $past(FSM_q)==EXEC) |-> IR_q[15:0] == $past(din));

  // pred_q update
  assert property ($past(clken) |-> pred_q == (($past(FSM_q)==FET0) ? $past(pred_din) : $past(pred_d)));

  // FSM next-state checks
  // FET0
  assert property ($past(clken) && $past(FSM_q)==FET0 |-> 
    FSM_q == ($past(din[IRLEN]) ? FET1
             : (!$past(pred_din)) ? FET0
             : ((($past(din[11:8])==LD)||($past(din[11:8])==STO)||($past(op_d)==PUSH)||($past(op_d)==POP)) ? EAD : EXEC)));

  // FET1
  assert property ($past(clken) && $past(FSM_q)==FET1 |-> 
    FSM_q == ((!$past(pred_q)) ? FET0 : ((($past(IR_q[3:0])!=4'h0) || $past(IR_q[IRLD]) || $past(IR_q[IRSTO])) ? EAD : EXEC)));

  // EAD
  assert property ($past(clken) && $past(FSM_q)==EAD |-> 
    FSM_q == ($past(IR_q[IRLD]) ? RDM : ($past(IR_q[IRSTO]) ? WRM : EXEC)));

  // RDM
  assert property ($past(clken) && $past(FSM_q)==RDM |-> FSM_q == EXEC);

  // WRM
  assert property ($past(clken) && $past(FSM_q)==WRM |-> 
    FSM_q == (((!(&$past(int_b))) && $past(PSR_q[EI])) ? INT : FET0));

  // EXEC
  assert property ($past(clken) && $past(FSM_q)==EXEC |-> 
    FSM_q == (((!(&$past(int_b)) && $past(PSR_q[EI])) || (($past(op)==PPSR) && (|$past(swiid)))) ? INT
             : ((($past(IR_q[3:0])==4'hF) || ($past(op)==JSR)) ? FET0
                : ($past(din[IRLEN]) ? FET1
                   : ((($past(din[11:8])==LD)||($past(din[11:8])==STO)||($past(op_d)==POP)||($past(op_d)==PUSH)) ? EAD
                      : ($past(pred_d) ? EXEC : FET0))))));

  // INT -> FET0 (default branch)
  assert property ($past(clken) && $past(FSM_q)==INT |-> FSM_q == FET0);

  // PC update rules
  assert property ($past(clken) && ($past(FSM_q)==FET0 || $past(FSM_q)==FET1) |-> PC_q == $past(PC_q)+16'd1);

  // INT state side-effects
  assert property (clken && FSM_q==INT |-> 
    (PC_q == ((!int_b[1]) ? INT_VECTOR1 : INT_VECTOR0)) &&
    (PCI_q == $past(PC_q)) &&
    (PSRI_q == $past(PSR_q[3:0])) &&
    (PSR_q[EI]==1'b0));

  // EXEC RTI side-effects
  assert property ($past(clken) && $past(FSM_q)==EXEC && $past(op)==RTI |-> 
    (PC_q == $past(PCI_q)) && (PSR_q == {4'b0,$past(PSRI_q)}));

  // PSR update (non-RTI)
  assert property ($past(clken) && $past(FSM_q)==EXEC && $past(op)!=RTI |-> 
    PSR_q == {$past(swiid),$past(enable_int),$past(sign),$past(carry),$past(zero)});

  // Flags basic consistency when writing from ALU (not PPSR and dst != PC)
  assert property ((op!=PPSR) && (IR_q[3:0]!=4'hF) |-> (zero == (~|result)) && (sign == result[15]));

  // Coverage
  cover property (FSM_q==FET0);
  cover property (FSM_q==FET1);
  cover property (FSM_q==EAD);
  cover property (FSM_q==RDM);
  cover property (FSM_q==WRM);
  cover property (FSM_q==EXEC);
  cover property (FSM_q==INT);
  cover property (clken && FSM_q==INT && ((!int_b[1]) || (!int_b[0]))); // interrupt taken
  cover property (clken && (FSM_q==RDM) && vio); // I/O read
  cover property (clken && (FSM_q==WRM) && vio); // I/O write
  cover property (clken && (FSM_q==RDM) && vda); // memory read
  cover property (clken && (FSM_q==WRM) && vda); // memory write
  cover property ($past(clken) && $past(FSM_q)==EXEC && $past(op)==JSR);
  cover property ($past(clken) && $past(FSM_q)==EXEC && $past(op)==RTI);

endmodule

// Helper to access instance scope in bind
module bind_target(); endmodule

// Example bind (place in testbench or a package once):
// bind opc6cpu opc6cpu_sva svai();