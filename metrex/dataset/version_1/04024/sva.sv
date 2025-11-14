// SVA for shift_register
// Checks synchronous active-low reset, load behavior, and shift behavior.
// Includes concise coverage of key scenarios.

module shift_register_sva #(parameter int WIDTH = 8) (
  input logic              clk,
  input logic              reset,   // active-low, synchronous
  input logic              load,
  input logic              data,
  input logic [WIDTH-1:0]  q
);

  default clocking cb @(posedge clk); endclocking

  // Ensure $past is valid before use
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Inputs should be known each cycle
  a_inputs_known: assert property (!$isunknown({reset, load, data}));

  // Synchronous active-low reset clears register next cycle
  a_reset_clear: assert property (reset == 1'b0 |=> q == '0);

  // Load behavior: next q is zero-extended data (matches RTL)
  a_load_path: assert property (disable iff (reset == 1'b0)
                                past_valid && load |=> q == {{(WIDTH-1){1'b0}}, $past(data)});

  // Shift behavior: shift left with serial-in at LSB
  a_shift_path: assert property (disable iff (reset == 1'b0)
                                 past_valid && !load |=> q == {$past(q[WIDTH-2:0]), $past(data)});

  // Optional bitflow check (redundant but precise mapping)
  a_bitflow: assert property (disable iff (reset == 1'b0)
                              past_valid && !load |=> q[WIDTH-1:1] == $past(q[WIDTH-2:0]) && q[0] == $past(data));

  // Coverage: see reset, load with 0/1, and shift with 0/1
  c_reset_pulse:  cover property (reset == 1'b0);
  c_load0:        cover property (reset && load && data == 1'b0);
  c_load1:        cover property (reset && load && data == 1'b1);
  c_shift0:       cover property (reset && !load && data == 1'b0);
  c_shift1:       cover property (reset && !load && data == 1'b1);

  // Coverage: observe a '1' walking to MSB after load then (WIDTH-1) shifts with data==1
  c_walk1_to_msb: cover property (reset && load && data
                                  ##1 (reset && !load && data)[* (WIDTH-1)]
                                  ##1 q[WIDTH-1]);

endmodule

// Bind into DUT
bind shift_register shift_register_sva #(.WIDTH(8)) shift_register_sva_i (
  .clk(clk), .reset(reset), .load(load), .data(data), .q(q)
);