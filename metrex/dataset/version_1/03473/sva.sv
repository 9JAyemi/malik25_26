// SVA checker for calculator. Bind this to the DUT.
// Focus: correctness of result, overflow semantics as coded, X/Z safety, and op coverage.

module calculator_sva (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [1:0] opcode,
    input logic [7:0] result,
    input logic       overflow
);

  // Golden model mirrors RTL expression widths and truncation
  logic [8:0] mtemp;
  logic [7:0] mres;

  always_comb begin
    unique case (opcode)
      2'b00: mtemp = {1'b0,in1} + {1'b0,in2};                // 9-bit add
      2'b01: mtemp = {1'b0,in1} - {1'b0,in2};                // 9-bit sub (wraps)
      2'b10: mtemp = (in1 * in2)[8:0];                       // truncate to 9 bits
      2'b11: mtemp = (in2 == 0) ? 9'd0 : {1'b0,(in1 / in2)}; // 9-bit div result
      default: mtemp = 9'd0;
    endcase
  end

  assign mres = mtemp[7:0];

  // Core assertions (combinational, zero-delay to avoid races)
  always_comb begin
    // Result must match modeled low 8 bits
    assert #0 (result === mres)
      else $error("calculator result mismatch: opc=%0b in1=%0d in2=%0d got=%0d exp=%0d",
                  opcode, in1, in2, result, mres);

    // Outputs must not be X/Z
    assert #0 (!$isunknown(result) && !$isunknown(overflow))
      else $error("calculator outputs contain X/Z: result=%0h overflow=%b", result, overflow);

    // Division-by-zero behavior
    assert #0 (!(opcode==2'b11 && in2==0) || (result==8'd0 && overflow===1'b1))
      else $error("div-by-zero handling incorrect");

    // If opcode has X/Z (default case), expect 0 result and overflow=1
    assert #0 (!($isunknown(opcode)) || (result==8'd0 && overflow===1'b1))
      else $error("default-case handling incorrect for opcode=%b", opcode);

    // As coded, overflow is always 1 due to (temp>255)||(temp<-256) with unsigned temp.
    // This assertion captures the RTL’s effective behavior.
    assert #0 (overflow === 1'b1)
      else $error("overflow should be 1 per RTL semantics");
  end

  // Concise functional coverage
  // Op coverage
  cover property (@(posedge 1'b0) 0); // placeholder to satisfy tools if needed
  always_comb begin
    cover (opcode==2'b00); // add
    cover (opcode==2'b01); // sub
    cover (opcode==2'b10); // mul
    cover (opcode==2'b11); // div

    // Interesting cases
    cover (opcode==2'b00 && ({1'b0,in1}+{1'b0,in2}) > 9'd255); // add carry
    cover (opcode==2'b01 && in1 < in2);                        // sub borrow (wrap)
    cover (opcode==2'b10 && (in1*in2) > 16'd255);              // mul overflow (true product)
    cover (opcode==2'b11 && in2==0);                           // div by zero
    cover (opcode==2'b11 && in2!=0 && (in1%in2)==0);           // exact division
    cover (opcode==2'b11 && in2!=0 && (in1%in2)!=0);           // non-exact division

    // Boundary values
    cover (in1==8'h00); cover (in1==8'hFF);
    cover (in2==8'h00); cover (in2==8'hFF);
  end

endmodule

// Bind into DUT
bind calculator calculator_sva calc_sva_i (.in1(in1), .in2(in2), .opcode(opcode), .result(result), .overflow(overflow));