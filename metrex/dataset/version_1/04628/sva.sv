Below is a concise, high-quality SVA package to check and cover my_module. It samples on a provided clock. Bind this checker to the DUT and connect a testbench clock.

module my_module_sva (
  input logic                clk,
  input logic [3:0]          in_data,
  input logic [1:0]          sel,
  input logic [1:0]          out_data
);
  default clocking cb @(posedge clk); endclocking

  // Known-ness: if inputs are known, output must be known
  assert property (!$isunknown({sel,in_data}) |-> !$isunknown(out_data));

  // Functional correctness per case item (use case-equality to match DUT case semantics)
  assert property ((sel===2'b00 && !$isunknown(in_data)) |-> out_data == ((~in_data + 4'd1) & 2'b11));
  assert property ((sel===2'b01 && !$isunknown(in_data)) |-> out_data == {in_data[0],1'b0});

  // Default path (covers sel==2'b10, 2'b11, and any sel with X/Z bits)
  assert property ((sel!==2'b00 && sel!==2'b01) |-> out_data == 2'b00);

  // Combinational stability: stable inputs imply stable output across cycles
  assert property ($stable({sel,in_data}) |-> $stable(out_data));

  // Coverage: exercise each decode and all 2-bit output values
  cover property (sel===2'b00);
  cover property (sel===2'b01);
  cover property (sel!==2'b00 && sel!==2'b01);

  cover property (out_data==2'b00);
  cover property (out_data==2'b01);
  cover property (out_data==2'b10);
  cover property (out_data==2'b11);
endmodule

// Example bind (edit clk path to your TB clock):
// bind my_module my_module_sva u_my_module_sva ( .clk(tb.clk), .in_data(in_data), .sel(sel), .out_data(out_data) );