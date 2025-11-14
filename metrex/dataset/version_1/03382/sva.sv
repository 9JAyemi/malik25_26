// SVA checker bound to shift_register. Focused, high-quality properties.
module shift_register_sva (
  input logic        clk,
  input logic [3:0]  inp,
  input logic [15:0] arr_out,
  input logic [15:0] arr
);
  default clocking cb @ (posedge clk); endclocking

  // Past-valid window for $past depth guarding (supports up to 16-cycle history)
  logic [16:0] pv;
  initial pv = '0;
  always_ff @(posedge clk) pv <= {pv[15:0], 1'b1};

  // Combinational mapping to output must always hold
  assert property (arr_out == {arr[15:4], inp})
    else $error("arr_out mismatch");

  // State update: registered shift must match previous cycle values
  assert property (pv[1] |-> arr == {$past(arr)[14:0], $past(inp[3])})
    else $error("arr update mismatch");

  // Strong per-bit shift relation: arr[k] is inp[3] delayed k+1 cycles
  genvar k;
  generate
    for (k=0; k<16; k++) begin : g_shift_bits
      assert property (pv[k+1] |-> arr[k] == $past(inp[3], k+1))
        else $error("arr[%0d] != $past(inp[3], %0d)", k, k+1);
    end
  endgenerate

  // X/Z checks on observable IOs (after first cycle)
  assert property (pv[1] |-> !$isunknown({inp, arr_out}))
    else $error("X/Z detected on inp/arr_out");
  
  // Lightweight functional coverage
  cover property (pv[16] && arr == '0);       // saw all-zeros state
  cover property (pv[16] && arr == '1);       // saw all-ones state
  cover property (pv[16] && arr[15] && !arr[14]); // a '1' propagated to MSB
  cover property (inp == 4'h0);
  cover property (inp == 4'hF);
endmodule

// Bind into DUT to access internal 'arr'
bind shift_register shift_register_sva sva_i (
  .clk     (clk),
  .inp     (inp),
  .arr_out (arr_out),
  .arr     (arr)
);