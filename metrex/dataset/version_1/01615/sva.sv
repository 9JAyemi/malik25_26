// SVA for top_module
// Focus: functional correctness, corner cases, and concise coverage.
// Bind this file to the DUT: bind top_module top_module_sva u_top_module_sva();

module top_module_sva;

  // Access DUT scope directly (bound into instance)
  // Signals assumed from DUT: clk, load, ena, data, q, shift_reg, shift_amt, shifted_data

  // Past-valid to avoid first-cycle $past issues
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Helpers
  function automatic [99:0] rotl3_100(input [99:0] x);
    return {x[96:0], x[99:97]};
  endfunction

  function automatic [99:0] rotr3_100(input [99:0] x);
    return {x[2:0], x[99:3]};
  endfunction

  function automatic [99:0] rol_k_100(input [99:0] x, input int k);
    int kk; begin
      kk = ((k % 100) + 100) % 100;
      return (kk==0) ? x : ({x,x} << kk)[199:100];
    end
  endfunction

  function automatic [99:0] ror_k_100(input [99:0] x, input int k);
    int kk; begin
      kk = ((k % 100) + 100) % 100;
      return (kk==0) ? x : ({x,x} >> kk)[99:0];
    end
  endfunction

  // 1) Combinational mux on q must match intended behavior (per comments)
  //    00: no rotation; 01: rotl3; 10: rotr3; 11: pass-through (load)
  property p_q_mux;
    1'b1 |-> ((ena==2'b00) -> (q == shifted_data))
          && ((ena==2'b01) -> (q == rotl3_100(shifted_data)))
          && ((ena==2'b10) -> (q == rotr3_100(shifted_data)))
          && ((ena==2'b11) -> (q == shift_reg));
  endproperty
  assert property (p_q_mux);

  // 2) Barrel shifter correctness: shifted_data should be a true rotate by |shift_amt|
  //    Sign of shift_amt selects direction: negative=right, non-negative=left.
  //    Uses signed interpretation to detect “-3” intent correctly.
  function automatic [99:0] expected_shifted(input [99:0] sr, input logic signed [2:0] s);
    int k; begin
      k = (s < 0) ? -s : s;
      return (s < 0) ? ror_k_100(sr, k) : rol_k_100(sr, k);
    end
  endfunction
  assert property (shifted_data == expected_shifted(shift_reg, $signed(shift_amt)));

  // 3) Sequential updates: load and shift/rotate pipeline
  //    On load: capture data and set +3
  assert property (load |=> (shift_reg == $past(data)) && ($signed(shift_amt) == 3));
  //    Else: shift_reg follows shifted_data; shift_amt encodes dir: ena==10 -> -3, else +3
  assert property (!load |=> (shift_reg == $past(shifted_data))
                               && ($signed(shift_amt) == (($past(ena)==2'b10) ? -3 : 3)));

  // 4) Sanity: shift_amt is always either +3 or -3 (signed), no X/Z on key signals
  assert property ($onehot0(ena)); // legal 2-bit value
  assert property ($signed(shift_amt) inside {3, -3});
  assert property (!$isunknown({ena,load,shift_amt,shift_reg,shifted_data,q})));

  // 5) Concise functional coverage
  cover property (load ##1 !load);                 // exercise both seq branches
  cover property (ena==2'b00);                     // no-rotation path
  cover property (ena==2'b01);                     // left-rotate path
  cover property (ena==2'b10);                     // right-rotate path
  cover property (ena==2'b11);                     // pass-through path
  cover property ($signed(shift_amt)==-3);         // negative-encoded amount observed
  cover property ($changed(shift_reg));            // state updates happening
  cover property (ena==2'b01 && q==rotl3_100(shifted_data));
  cover property (ena==2'b10 && q==rotr3_100(shifted_data));

endmodule

// Bind into DUT instance(s)
bind top_module top_module_sva u_top_module_sva();