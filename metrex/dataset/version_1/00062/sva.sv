// SVA checker for ExShad64
// Bind this module to the DUT: bind ExShad64 ExShad64_sva u_exshad64_sva(.*);

module ExShad64_sva (
  input logic         clock,
  input logic         reset,
  input logic [63:0]  valRs,
  input logic [7:0]   valRt,
  input logic [2:0]   shOp,
  input logic [63:0]  valRn
);

  // Golden model: op0=pass, op1=LSL, op2/4=ASR, op3=LSR (shift amount = valRt[5:0])
  function automatic logic [63:0] model_shift
    (input logic [63:0] rs, input logic [7:0] rt, input logic [2:0] op);
    logic [5:0] amt;
    logic signed [63:0] srs;
    begin
      amt = rt[5:0];
      srs = rs;
      unique case (op)
        3'h0: model_shift = rs;
        3'h1: model_shift = rs << amt;      // logical left
        3'h2: model_shift = srs >>> amt;    // arithmetic right
        3'h3: model_shift = rs >> amt;      // logical right
        3'h4: model_shift = srs >>> amt;    // arithmetic right
        default: model_shift = rs;
      endcase
    end
  endfunction

  // No-X propagation: clean inputs => clean output
  property p_no_x_out;
    @(posedge clock) disable iff (reset)
      (!$isunknown({shOp, valRt, valRs})) |-> (!$isunknown(valRn));
  endproperty
  a_no_x_out: assert property (p_no_x_out);

  // Functional correctness against golden model
  property p_functional;
    @(posedge clock) disable iff (reset)
      (!$isunknown({shOp, valRt, valRs})) |-> (valRn === model_shift(valRs, valRt, shOp));
  endproperty
  a_functional: assert property (p_functional);

  // Basic safety: output width and stability on identical inputs
  property p_idempotent_zero_shift;
    @(posedge clock) disable iff (reset)
      (!$isunknown({valRt, shOp, valRs}) && (valRt[5:0] == 6'd0)) |->
        (valRn === ((shOp==3'h1) ? valRs :
                    (shOp==3'h2) ? valRs :
                    (shOp==3'h3) ? valRs :
                    (shOp==3'h4) ? valRs : valRs));
  endproperty
  a_idempotent_zero_shift: assert property (p_idempotent_zero_shift);

  // Lightweight functional covers (ops, edge shift amounts, sign behaviors)
  cover property (@(posedge clock) disable iff (reset) shOp==3'h0);

  // LSL edges
  cover property (@(posedge clock) disable iff (reset) shOp==3'h1 && valRt==8'h00);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h1 && valRt==8'h01);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h1 && valRt[5:0]==6'd31);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h1 && valRt[5:0]==6'd32);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h1 && valRt[5:0]==6'd63);

  // LSR edges
  cover property (@(posedge clock) disable iff (reset) shOp==3'h3 && valRt==8'h00);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h3 && valRt[5:0]==6'd01);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h3 && valRt[5:0]==6'd63);

  // ASR with sign=0 and sign=1
  cover property (@(posedge clock) disable iff (reset) shOp==3'h2 && valRs[63]==1'b0 && valRt[5:0]==6'd08);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h2 && valRs[63]==1'b1 && valRt[5:0]==6'd08);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h4 && valRs[63]==1'b0 && valRt[5:0]==6'd16);
  cover property (@(posedge clock) disable iff (reset) shOp==3'h4 && valRs[63]==1'b1 && valRt[5:0]==6'd16);

  // Exercise upper bits of valRt (bit6/bit7), while amount uses [5:0]
  cover property (@(posedge clock) disable iff (reset) shOp==3'h1 && valRt==8'h40); // amt=0 with bit6=1
  cover property (@(posedge clock) disable iff (reset) shOp==3'h3 && valRt==8'hC1); // amt=1 with bit7=1

endmodule