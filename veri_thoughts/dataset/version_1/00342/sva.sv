// SVA for shift_register
module shift_register_sva
(
  input  logic        clk,
  input  logic        shift_dir,
  input  logic        parallel_load,
  input  logic [7:0]  data_in,
  input  logic [7:0]  serial_out,
  input  logic [7:0]  parallel_out
);

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Combinational ties
  assert property (@(posedge clk) serial_out[0] == parallel_out[0]);
  assert property (@(posedge clk) serial_out[7:1] == '0);

  // No X on outputs after the first cycle
  assert property (@(posedge clk) past_valid |-> !$isunknown({parallel_out, serial_out}));

  // Parallel load next-state
  assert property (@(posedge clk)
    past_valid && $past(parallel_load)
    |-> parallel_out == $past(data_in)
        && serial_out[0] == $past(data_in[0])
        && serial_out[7:1] == '0
  );

  // Left shift (shift_dir==1) next-state
  assert property (@(posedge clk)
    past_valid && $past(!parallel_load && shift_dir)
    |-> parallel_out == { $past(parallel_out[6:0]), 1'b0 }
        && serial_out[0] == 1'b0
        && serial_out[7:1] == '0
  );

  // Right shift (shift_dir==0) next-state
  assert property (@(posedge clk)
    past_valid && $past(!parallel_load && !shift_dir)
    |-> parallel_out == { 1'b0, $past(parallel_out[7:1]) }
        && serial_out[0] == $past(parallel_out[1])
        && serial_out[7:1] == '0
  );

  // Functional coverage
  cover property (@(posedge clk) parallel_load);
  cover property (@(posedge clk) !parallel_load && shift_dir);
  cover property (@(posedge clk) !parallel_load && !shift_dir);
  cover property (@(posedge clk) parallel_load ##1 (!parallel_load && shift_dir));
  cover property (@(posedge clk) parallel_load ##1 (!parallel_load && !shift_dir));
  // Load then 8 left shifts to zero
  cover property (@(posedge clk)
    parallel_load ##1 (!parallel_load && shift_dir)[*8] ##1 (parallel_out == '0)
  );
  // Load then 8 right shifts to zero
  cover property (@(posedge clk)
    parallel_load ##1 (!parallel_load && !shift_dir)[*8] ##1 (parallel_out == '0)
  );

endmodule

// Bind into DUT
bind shift_register shift_register_sva u_shift_register_sva (
  .clk          (clk),
  .shift_dir    (shift_dir),
  .parallel_load(parallel_load),
  .data_in      (data_in),
  .serial_out   (serial_out),
  .parallel_out (parallel_out)
);