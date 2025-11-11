// SVA for top_module hierarchy
module top_module_sva (
  input logic         clk,
  input logic         load,
  input logic [1:0]   ena,
  input logic [99:0]  in,
  input logic [99:0]  rotated_data,
  input logic [2:0]   comb_out,
  input logic [7:0]   final_out,
  input logic [7:0]   q
);

  // Track whether we've seen at least one load (avoid X-based false failures)
  logic got_load;
  initial got_load = 1'b0;
  always_ff @(posedge clk) if (load) got_load <= 1'b1;

  // Basic x/z checks on control
  assert property (@(posedge clk) !$isunknown({load,ena}));

  // Rotator behavior
  // Load dominates and captures input data
  assert property (@(posedge clk) load |=> rotated_data == $past(in));

  // No enable => hold value
  assert property (@(posedge clk) got_load && !load && (ena == 2'b00)
                   |=> rotated_data == $past(rotated_data));

  // Left rotate when ena[0] set (priority over ena[1])
  assert property (@(posedge clk) got_load && !load && ena[0]
                   |=> rotated_data == { $past(rotated_data[98:0]),
                                          $past(rotated_data[99]) });

  // Right path when only ena[1] set (matches DUT code semantics)
  assert property (@(posedge clk) got_load && !load && !ena[0] && ena[1]
                   |=> rotated_data == { $past(rotated_data[1 +: 99]),
                                          $past(rotated_data[0]) });

  // Combinational reductions correct
  assert property (@(posedge clk) comb_out[0] == &rotated_data);
  assert property (@(posedge clk) comb_out[1] == |rotated_data);
  assert property (@(posedge clk) comb_out[2] == ^rotated_data);

  // Legal value set for reduction tuple (based on 100-bit width)
  assert property (@(posedge clk) comb_out inside {3'b000,3'b010,3'b011,3'b110});

  // final_module mapping (q is driven by final_out)
  assert property (@(posedge clk) q == final_out);

  // Functional mapping of q
  assert property (@(posedge clk) comb_out == 3'b000 |-> q == rotated_data[7:0]);          // pass-through
  assert property (@(posedge clk) comb_out == 3'b001 |-> q == 8'hFF);                      // OR  with 0xFF
  assert property (@(posedge clk) comb_out == 3'b010 |-> q == ~rotated_data[7:0]);         // XOR with 0xFF
  assert property (@(posedge clk) comb_out == 3'b011 |-> q == rotated_data[7:0] + 8'h01);  // +1
  assert property (@(posedge clk) comb_out == 3'b100 |-> q == rotated_data[7:0] - 8'h01);  // -1
  assert property (@(posedge clk) comb_out inside {3'b101,3'b110,3'b111} |-> q == 8'h00);  // default

  // Coverage
  cover property (@(posedge clk) load);
  cover property (@(posedge clk) got_load && !load && (ena == 2'b00));
  cover property (@(posedge clk) got_load && !load && (ena == 2'b01)); // left
  cover property (@(posedge clk) got_load && !load && (ena == 2'b10)); // right-path per code
  cover property (@(posedge clk) got_load && !load && (ena == 2'b11)); // left due to priority

  cover property (@(posedge clk) comb_out == 3'b000);
  cover property (@(posedge clk) comb_out == 3'b010);
  cover property (@(posedge clk) comb_out == 3'b011);
  cover property (@(posedge clk) comb_out == 3'b110); // default path exercised

endmodule

// Bind into the DUT
bind top_module top_module_sva sva_i (
  .clk(clk),
  .load(load),
  .ena(ena),
  .in(in),
  .rotated_data(rotated_data),
  .comb_out(comb_out),
  .final_out(final_out),
  .q(q)
)