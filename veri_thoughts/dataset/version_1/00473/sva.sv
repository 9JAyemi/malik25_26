// SVA for Immediate_Extend
// Bindable, concise, full functional check + essential coverage

module Immediate_Extend_sva (
  input logic [31:0] data_out,
  input logic [2:0]  load,
  input logic [15:0] data_in
);

  function automatic logic [31:0] exp_out (logic [2:0] l, logic [15:0] din);
    logic [15:0] imm16;
    unique case (l)
      3'd0: imm16 = {{8{din[7]}},  din[7:0]};
      3'd1: imm16 = {{12{din[3]}}, din[3:0]};
      3'd2: imm16 = {{5{din[10]}}, din[10:0]};
      3'd3: imm16 = {12'b0,        din[3:0]};
      3'd4: imm16 = {8'b0,         din[7:0]};
      3'd5: imm16 = {{11{din[4]}}, din[4:0]};
      default: imm16 = {13'b0,     din[4:2]};
    endcase
    return {16'b0, imm16}; // RTL assigns 16-bit RHS into 32-bit -> zero-extends upper 16
  endfunction

  // Functional equivalence (golden) – single concise check
  property p_out_matches_golden;
    @(*) !$isunknown({load, data_in}) |-> (data_out == exp_out(load, data_in));
  endproperty
  assert property (p_out_matches_golden);

  // Upper half must always be zero due to zero-extension to 32 bits
  assert property (@(*) data_out[31:16] == 16'h0000);

  // Basic input sanity (helps find X/Z driving combinational logic)
  assert property (@(*) !$isunknown(load));
  assert property (@(*) !$isunknown(data_in));

  // Coverage: hit every mode; exercise sign-bit polarity in sign-extend modes
  cover property (@(*) load == 3'd0);
  cover property (@(*) load == 3'd1);
  cover property (@(*) load == 3'd2);
  cover property (@(*) load == 3'd3);
  cover property (@(*) load == 3'd4);
  cover property (@(*) load == 3'd5);
  cover property (@(*) load == 3'd6);
  cover property (@(*) load == 3'd7);

  cover property (@(*) (load==3'd0) && (data_in[7]  == 1'b0));
  cover property (@(*) (load==3'd0) && (data_in[7]  == 1'b1));
  cover property (@(*) (load==3'd1) && (data_in[3]  == 1'b0));
  cover property (@(*) (load==3'd1) && (data_in[3]  == 1'b1));
  cover property (@(*) (load==3'd2) && (data_in[10] == 1'b0));
  cover property (@(*) (load==3'd2) && (data_in[10] == 1'b1));
  cover property (@(*) (load==3'd5) && (data_in[4]  == 1'b0));
  cover property (@(*) (load==3'd5) && (data_in[4]  == 1'b1));

endmodule

// Bind into the DUT (use in testbench)
// bind Immediate_Extend Immediate_Extend_sva immext_sva_bind (.*);