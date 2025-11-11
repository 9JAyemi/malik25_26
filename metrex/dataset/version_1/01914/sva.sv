// SVA for AGrises
// Bind this file to the DUT without modifying the RTL.

module AGrises_sva #(
  parameter int DATA_WIDTH = 32,
  parameter int FIFO_DEPTH = 256,
  parameter int FIFO_DEPTH_LOG2 = 8
)(
  input  logic                         clk,
  input  logic                         rst,
  // DUT ports
  input  logic [DATA_WIDTH-1:0]        data_fifo_out,
  input  logic                         data_valid_fifo_out,
  input  logic [FIFO_DEPTH_LOG2:0]     usedw_fifo_out,
  input  logic [DATA_WIDTH-1:0]        data_fifo_in,
  input  logic [FIFO_DEPTH_LOG2:0]     usedw_fifo_in,
  input  logic                         start,
  input  logic                         read_fifo_in,
  input  logic                         endf,
  // Internal DUT regs/wires (bound hierarchically)
  input  logic [1:0]                   stages,
  input  logic                         stages_init,
  input  logic [1:0]                   run,
  input  logic [18:0]                  pixel_counter
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helper functions for expected pixel computation
  function automatic [7:0] exp_grey(input logic [DATA_WIDTH-1:0] rgb);
    logic [14:0] aux;
    logic [7:0]  up7;
    logic [7:0]  g;
    aux = (rgb[23:16] * 8'd30) + (rgb[15:8] * 8'd59) + (rgb[7:0] * 8'd11);
    up7 = aux[14:8];
    g   = (up7 << 1);
    g   = g + (up7 >> 1);
    g   = g + (up7 / 8'd19);
    g   = g + (aux[7:0] >> 6);
    return g;
  endfunction

  function automatic [DATA_WIDTH-1:0] exp_out(input logic [DATA_WIDTH-1:0] rgb);
    logic [7:0] g;
    g = exp_grey(rgb);
    return {8'h00, {3{g}}};
  endfunction

  // Combinational mapping checks
  assert property (endf == (run == 2));
  assert property (data_valid_fifo_out == ((run == 1) && (stages == 2)));
  assert property (read_fifo_in == ((run == 1) && (stages == 1)));
  assert property (stages_init == (((usedw_fifo_in > 32) || (pixel_counter < 19'd33)) &&
                                   (usedw_fifo_out < FIFO_DEPTH) &&
                                   (run == 1) && (stages == 0)) );

  // Encodings
  assert property (run inside {2'd0,2'd1,2'd2});
  assert property (stages inside {2'd0,2'd1,2'd2});

  // Start effects (next-cycle)
  assert property (start |=> (run == 2'd1));
  assert property (start |=> (pixel_counter == 19'd384000));
  assert property (start |=> (stages == 2'd0));

  // Pixel counter behavior
  assert property ((!start && data_valid_fifo_out) |=> pixel_counter == $past(pixel_counter) - 19'd1);
  assert property ((!start && !data_valid_fifo_out) |=> pixel_counter == $past(pixel_counter));

  // Run/endf handshake: run==2 is a 1-cycle state (unless preempted by start)
  assert property ((run == 2'd2 && !start) |=> run == 2'd0);

  // Stage pipeline progression (preempted by start)
  assert property (disable iff (rst || start)
                   stages_init |=> ##1 (stages == 2'd1) ##1 (stages == 2'd2) ##1 (stages == 2'd0));

  // Output pixel correctness relative to input two cycles earlier
  assert property (data_valid_fifo_out |-> ($past(stages_init,2) &&
                                           data_fifo_out == exp_out($past(data_fifo_in,2))));

  // FIFOs: bounds and safe usage
  assert property (usedw_fifo_in  <= FIFO_DEPTH);
  assert property (usedw_fifo_out <= FIFO_DEPTH);
  assert property (read_fifo_in |-> (usedw_fifo_in > 0));
  assert property (data_valid_fifo_out |-> (usedw_fifo_out < FIFO_DEPTH));

  // Basic covers
  cover property (start ##1 run == 2'd1);
  cover property (stages_init ##1 stages == 2'd1 ##1 stages == 2'd2 ##1 data_valid_fifo_out);
  cover property (run == 2'd2 ##1 run == 2'd0);

endmodule

// Bind to DUT (connect internals via hierarchical names)
bind AGrises AGrises_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .FIFO_DEPTH(FIFO_DEPTH),
  .FIFO_DEPTH_LOG2(FIFO_DEPTH_LOG2)
) AGrises_sva_i (
  .clk(clk),
  .rst(rst),
  .data_fifo_out(data_fifo_out),
  .data_valid_fifo_out(data_valid_fifo_out),
  .usedw_fifo_out(usedw_fifo_out),
  .data_fifo_in(data_fifo_in),
  .usedw_fifo_in(usedw_fifo_in),
  .start(start),
  .read_fifo_in(read_fifo_in),
  .endf(endf),
  .stages(stages),
  .stages_init(stages_init),
  .run(run),
  .pixel_counter(pixel_counter)
);