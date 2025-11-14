// SVA checker for barrel_shifter
// Binds into DUT and verifies combinational behavior and branch coverage
module barrel_shifter_sva;

  // Reference functions that mirror the RTL (including truncation behavior)
  function automatic logic [15:0] f_s2 (logic [15:0] data, logic [1:0] ctrl);
    case (ctrl)
      2'b00: f_s2 = {data[14:0], 1'b0};           // LSL1
      2'b01: f_s2 = {1'b0, data[15:1]};           // LSR1
      2'b10: f_s2 = {data[15:1], data[15]};       // RTL's truncated concat
      default: f_s2 = {data[0], data[15:1]};      // ROR1
    endcase
  endfunction

  function automatic logic [15:0] f_s3 (logic [15:0] s2, logic [3:0] shift);
    if (shift[3])       f_s3 = s2;
    else if (shift[2])  f_s3 = s2 >> 2;
    else if (shift[1])  f_s3 = s2 >> 4;
    else                f_s3 = s2 >> 8;
  endfunction

  function automatic logic [15:0] f_out (logic [15:0] s3, logic [3:0] shift);
    if (shift[0])                 f_out = s3;                         // pass-through
    else if (shift[1])            f_out = {s3[15:1], s3[15]};         // RTL's truncated concat
    else                          f_out = {s3[14:0], s3[0]};          // ROL1
  endfunction

  logic [15:0] s2_m, s3_m, out_m;

  // Combinational assertions (evaluate in zero time on any change)
  always_comb begin
    s2_m  = f_s2(DATA, CTRL);
    s3_m  = f_s3(s2_m, SHIFT);
    out_m = f_out(s3_m, SHIFT);

    assert #0 (shift_reg1 == DATA)
      else $error("shift_reg1 != DATA");

    assert #0 (shift_reg2 == s2_m)
      else $error("shift_reg2 mismatch CTRL=%b DATA=%h exp=%h got=%h", CTRL, DATA, s2_m, shift_reg2);

    assert #0 (shift_reg3 == s3_m)
      else $error("shift_reg3 mismatch SHIFT[3:1]=%b exp=%h got=%h", SHIFT[3:1], s3_m, shift_reg3);

    assert #0 (out == out_m)
      else $error("out mismatch CTRL=%b SHIFT=%b exp=%h got=%h", CTRL, SHIFT, out_m, out);

    // No X/Z on internal/output when inputs are known
    if (!$isunknown({DATA, SHIFT, CTRL})) begin
      assert #0 (!$isunknown({shift_reg2, shift_reg3, out}))
        else $error("X/Z detected on internal/output with known inputs");
    end

    // Guard the shadowed branch intent: when SHIFT[1:0]==01, first if should dominate
    if (SHIFT[1:0]==2'b01) begin
      assert #0 (out == shift_reg3)
        else $error("For SHIFT[1:0]==01, out must equal shift_reg3");
    end
  end

  // Minimal functional coverage to hit all control/shift branches
  // CTRL decode
  cover (CTRL==2'b00);
  cover (CTRL==2'b01);
  cover (CTRL==2'b10);
  cover (CTRL==2'b11);
  // SHIFT stage-3 priority branches
  cover (SHIFT[3]);
  cover (!SHIFT[3] && SHIFT[2]);
  cover (!SHIFT[3] && !SHIFT[2] && SHIFT[1]);
  cover (!SHIFT[3] && !SHIFT[2] && !SHIFT[1]);
  // Final out selection
  cover (SHIFT[0]);                 // pass-through
  cover (!SHIFT[0] && SHIFT[1]);    // truncated-concat branch
  cover (!SHIFT[0] && !SHIFT[1]);   // rotate-left branch
  cover (SHIFT[1:0]==2'b01);        // shadowed input combination exercised
  // Sign-related coverage for CTRL==2'b10 path
  cover (CTRL==2'b10 && DATA[15]==1'b1);
  cover (CTRL==2'b10 && DATA[15]==1'b0);

endmodule

bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva();