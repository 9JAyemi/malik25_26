// SVA for dectohexstr8
module dectohexstr8_sva(input logic [7:0] in, input logic [15:0] out);

  default clocking cb @($global_clock); endclocking

  function automatic logic [7:0] ascii_hex(input logic [3:0] n);
    ascii_hex = (n <= 4'd9) ? (8'h30 + n) : (8'h41 + (n - 4'd10));
  endfunction

  // Functional mapping
  assert property (!$isunknown(in[3:0]) |-> out[7:0]   == ascii_hex(in[3:0]));
  assert property (!$isunknown(in[7:4]) |-> out[15:8]  == ascii_hex(in[7:4]));
  assert property (!$isunknown(in)      |-> {out[15:8],out[7:0]} == {ascii_hex(in[7:4]),ascii_hex(in[3:0])});

  // Valid ASCII hex outputs
  assert property (!$isunknown(out[7:0])  |-> out[7:0]  inside {"0","1","2","3","4","5","6","7","8","9","A","B","C","D","E","F"});
  assert property (!$isunknown(out[15:8]) |-> out[15:8] inside {"0","1","2","3","4","5","6","7","8","9","A","B","C","D","E","F"});

  // No X/Z propagation when inputs are known
  assert property (!$isunknown(in) |-> !$isunknown(out));

  // Independence of nibbles
  assert property ($changed(in[7:4]) && $stable(in[3:0]) |-> $stable(out[7:0]));
  assert property ($changed(in[3:0]) && $stable(in[7:4]) |-> $stable(out[15:8]));

  // Equal ASCII iff equal nibble values (when known)
  assert property (!$isunknown(in) |-> ((out[15:8]==out[7:0]) == (in[7:4]==in[3:0])));

  // Coverage: hit all 16 values on each nibble with correct mapping
  genvar v;
  generate
    for (v=0; v<16; v++) begin: COV
      cover property (in[3:0] == v[3:0] && out[7:0]   == ascii_hex(v[3:0]));
      cover property (in[7:4] == v[3:0] && out[15:8]  == ascii_hex(v[3:0]));
    end
  endgenerate

  // Corner cases and independence activity
  cover property (in == 8'h00 && out == {"0","0"});
  cover property (in == 8'hFF && out == {"F","F"});
  cover property ($changed(in[7:4]) && $stable(in[3:0]));
  cover property ($changed(in[3:0]) && $stable(in[7:4]));

endmodule

bind dectohexstr8 dectohexstr8_sva sva_inst(.in(in), .out(out));