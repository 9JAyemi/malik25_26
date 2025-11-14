// SVA checker for Arithmetic_Logic_Unit
// Bind example (provide clk/rst_n from your env):
// bind Arithmetic_Logic_Unit alu_sva u_alu_sva(.clk(clk), .rst_n(rst_n), .ctrl(ctrl), .data_in_A(data_in_A), .data_in_B(data_in_B), .data_out(data_out));

module alu_sva #(parameter WIDTH=16) (
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic [4:0]               ctrl,
  input  logic [WIDTH-1:0]         data_in_A,
  input  logic [WIDTH-1:0]         data_in_B,
  input  logic [WIDTH-1:0]         data_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic logic [WIDTH-1:0] ref_model(input logic [4:0] c,
                                                 input logic [WIDTH-1:0] A,
                                                 input logic [WIDTH-1:0] B);
    case (c)
      5'd1 :  ref_model = A + B;
      5'd2 :  ref_model = A - B;
      5'd3 :  ref_model = A & B;
      5'd4 :  ref_model = A | B;
      5'd5 :  ref_model = A ^ B;
      5'd6 :  ref_model = ~A;
      5'd7 :  ref_model = ~B;
      5'd8 :  ref_model = A << 1;
      5'd9 :  ref_model = A >> 1;
      5'd10:  ref_model = B << 1;
      5'd11:  ref_model = B >> 1;
      5'd12:  ref_model = (A == B) ? {{(WIDTH-1){1'b0}},1'b1} : '0;
      5'd13:  ref_model = (A <  B) ? {{(WIDTH-1){1'b0}},1'b1} : '0;
      5'd14:  ref_model = (A >  B) ? {{(WIDTH-1){1'b0}},1'b1} : '0;
      5'd15:  ref_model = (A <= B) ? {{(WIDTH-1){1'b0}},1'b1} : '0;
      5'd16:  ref_model = (A >= B) ? {{(WIDTH-1){1'b0}},1'b1} : '0;
      default: ref_model = '0;
    endcase
  endfunction

  // Functional equivalence for all opcodes (including default)
  assert property (data_out == ref_model(ctrl, data_in_A, data_in_B))
    else $error("ALU mismatch: ctrl=%0d A=%0h B=%0h got=%0h exp=%0h",
                ctrl, data_in_A, data_in_B, data_out,
                ref_model(ctrl, data_in_A, data_in_B));

  // Output must be 2-state when inputs are 2-state
  assert property (!$isunknown({ctrl, data_in_A, data_in_B}) |-> !$isunknown(data_out))
    else $error("ALU X/Z on output with known inputs");

  // Comparators produce only 0 or 1
  assert property ((ctrl inside {5'd12,5'd13,5'd14,5'd15,5'd16})
                    |-> (data_out inside {16'h0000,16'h0001}));

  // Opcode hit coverage (1..16) and default
  genvar i;
  generate
    for (i = 1; i <= 16; i++) begin : gen_cov_op
      cover property (ctrl == i);
    end
  endgenerate
  cover property (!(ctrl inside {[5'd1:5'd16]})); // default branch

  // Corner-case functional coverage
  cover property (ctrl==5'd1  && data_in_A==16'hFFFF && data_in_B==16'h0001 && data_out==16'h0000); // add wrap
  cover property (ctrl==5'd2  && data_in_A==16'h0000 && data_in_B==16'h0001 && data_out==16'hFFFF); // sub borrow
  cover property (ctrl==5'd8  && data_in_A==16'h8001 && data_out==16'h0002); // A<<1
  cover property (ctrl==5'd9  && data_in_A==16'h8001 && data_out==16'h4000); // A>>1
  cover property (ctrl==5'd10 && data_in_B==16'h8001 && data_out==16'h0002); // B<<1
  cover property (ctrl==5'd11 && data_in_B==16'h8001 && data_out==16'h4000); // B>>1

  // Comparator truth-table touch points
  cover property (ctrl==5'd12 && data_in_A==16'h1234 && data_in_B==16'h1234 && data_out==16'h0001); // ==
  cover property (ctrl==5'd13 && data_in_A==16'h0001 && data_in_B==16'h0002 && data_out==16'h0001); // <
  cover property (ctrl==5'd13 && data_in_A==16'h0002 && data_in_B==16'h0002 && data_out==16'h0000); // < false on =
  cover property (ctrl==5'd14 && data_in_A==16'h0002 && data_in_B==16'h0001 && data_out==16'h0001); // >
  cover property (ctrl==5'd14 && data_in_A==16'h0002 && data_in_B==16'h0002 && data_out==16'h0000); // > false on =
  cover property (ctrl==5'd15 && data_in_A==16'h0002 && data_in_B==16'h0002 && data_out==16'h0001); // <= true on =
  cover property (ctrl==5'd16 && data_in_A==16'h0002 && data_in_B==16'h0002 && data_out==16'h0001); // >= true on =

endmodule