// Bind these assertions to the DUT
bind calculator calc_sva_asrt();

module calc_sva_asrt;

  // Interface/outputs sanity (no X/Z)
  assert property (@(a or b or op or sel) !$isunknown({a,b,op,sel}));
  assert property (@(out or overflow) !$isunknown({out,overflow}));

  // a_mag/b_mag conversion (two's-complement magnitude as implemented)
  assert property (@(a) ##0 a_mag == (a[7] ? (~a + 8'h01) : a));
  assert property (@(b) ##0 b_mag == (b[7] ? (~b + 8'h01) : b));

  // op_sel decode from sel/op (sel is 4b; 0..3 explicit, others default to 2'b11)
  assert property (@(op or sel)
    1'b1 |-> ##0 (
      (sel==4'd0) ? (op_sel==op) :
      (sel==4'd1) ? (op_sel==2'b00) :
      (sel==4'd2) ? (op_sel==2'b01) :
      (sel==4'd3) ? (op_sel==2'b10) :
                    (op_sel==2'b11)
    )
  );

  // add_result matches selected operation (8-bit truncation as in RTL)
  assert property (@(a_mag or b_mag or op_sel)
    (op_sel==2'b00) |-> ##0 add_result == (a_mag + b_mag)
  );
  assert property (@(a_mag or b_mag or op_sel)
    (op_sel==2'b01) |-> ##0 add_result == (a_mag - b_mag)
  );
  assert property (@(a_mag or b_mag or op_sel)
    (op_sel==2'b10) |-> ##0 add_result == (a_mag * b_mag)
  );
  // Division-by-zero must not occur
  assert property (@(b_mag or op_sel) (op_sel==2'b11) |-> b_mag!=8'h00);
  assert property (@(a_mag or b_mag or op_sel)
    (op_sel==2'b11 && b_mag!=8'h00) |-> ##0 add_result == (a_mag / b_mag)
  );

  // Overflow flag = MSB != next-MSB of add_result
  assert property (@(add_result) ##0 overflow == (add_result[7] ^ add_result[6]));

  // Output selection: follow add_result when sel<4; hold otherwise (latch behavior)
  assert property (@(sel or add_result or op_sel)
    (sel < 4) |-> ##0 out == add_result
  );
  assert property (@(add_result or op_sel) (sel >= 4) |-> $stable(out));
  assert property (@(sel)                 (sel >= 4) |-> $stable(out));

  // Internals known after settle
  assert property (@(a or b or op or sel or a_mag or b_mag or op_sel or add_result)
    ##0 !$isunknown({a_mag,b_mag,op_sel,add_result})
  );

  // Coverage: exercise all ops, overflow, sel default path, and negative inputs
  cover property (@(op_sel) ##0 (op_sel==2'b00));
  cover property (@(op_sel) ##0 (op_sel==2'b01));
  cover property (@(op_sel) ##0 (op_sel==2'b10));
  cover property (@(op_sel) ##0 (op_sel==2'b11));
  cover property (@(sel or add_result) (sel<4) ##0 out==add_result);
  cover property (@(sel) (sel>=4));
  cover property (@(add_result) overflow);
  cover property (@(a or b) a[7]);
  cover property (@(a or b) b[7]);

endmodule