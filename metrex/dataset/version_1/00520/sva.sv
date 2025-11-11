// SVA for calculator. Bind this module to the DUT.
module calculator_sva (
  input  logic [31:0] A,
  input  logic [31:0] B,
  input  logic [1:0]  OPCODE,
  input  logic        RESET,
  input  logic [31:0] RESULT
);

  // Create a combinational sampling event on input changes
  event comb_ev;
  always @(A or B or OPCODE or RESET) -> comb_ev;

  // Golden reference function (matches RTL semantics including default and reset)
  function automatic logic [31:0] ref_calc
    (input logic [31:0] a, b,
     input logic [1:0]  opcode,
     input logic        rst);
    logic [31:0] r;
    if (rst) r = 32'd0;
    else begin
      unique case (opcode)
        2'b00: r = a + b;
        2'b01: r = a - b;
        2'b10: r = a * b;
        2'b11: r = a / b;
        default: r = 32'd0; // opcode X/Z -> default
      endcase
    end
    return r;
  endfunction

  // Functional equivalence (allowing 4-state with ===). Sample one delta after inputs change.
  property p_equiv;
    @(comb_ev) 1'b1 |-> ##0 (RESULT === ref_calc(A,B,OPCODE,RESET));
  endproperty
  assert property (p_equiv)
    else $error("RESULT mismatch: A=%0h B=%0h OPCODE=%b RESET=%b RESULT=%0h exp=%0h",
                A,B,OPCODE,RESET,RESULT,ref_calc(A,B,OPCODE,RESET));

  // Reset dominates
  assert property (@(comb_ev) RESET |-> ##0 (RESULT == 32'd0))
    else $error("RESET asserted but RESULT != 0");

  // No divide-by-zero when division selected (flag as error)
  assert property (@(comb_ev) (!RESET && (OPCODE==2'b11)) |-> (B != 32'd0))
    else $error("Illegal divide-by-zero: B==0");

  // Default case behavior when OPCODE is X/Z
  assert property (@(comb_ev) (!RESET && $isunknown(OPCODE)) |-> ##0 (RESULT == 32'd0))
    else $error("Unknown OPCODE did not map to default RESULT=0");

  // Known-result guarantee when all inputs are known and no div-by-zero
  assert property (@(comb_ev)
                   (!RESET && !$isunknown({A,B,OPCODE}) && !(OPCODE==2'b11 && (B==32'd0)))
                   |-> ##0 !$isunknown(RESULT))
    else $error("RESULT contains X/Z with known inputs and legal opcode");

  // Coverage: exercise each opcode path and reset, including illegal div-by-zero and default via unknown opcode
  cover property (@(comb_ev) !RESET && (OPCODE==2'b00) ##0 (RESULT === (A + B)));
  cover property (@(comb_ev) !RESET && (OPCODE==2'b01) ##0 (RESULT === (A - B)));
  cover property (@(comb_ev) !RESET && (OPCODE==2'b10) ##0 (RESULT === (A * B)));
  cover property (@(comb_ev) !RESET && (OPCODE==2'b11) && (B!=32'd0) ##0 (RESULT === (A / B)));
  cover property (@(comb_ev) RESET);
  cover property (@(comb_ev) !RESET && (OPCODE==2'b11) && (B==32'd0));          // illegal scenario seen
  cover property (@(comb_ev) !RESET && $isunknown(OPCODE) ##0 (RESULT==32'd0)); // default branch hit

endmodule

// Bind to DUT
bind calculator calculator_sva u_calculator_sva (
  .A(A), .B(B), .OPCODE(OPCODE), .RESET(RESET), .RESULT(RESULT)
);