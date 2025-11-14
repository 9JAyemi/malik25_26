// SVA for tmu2_burst
// Bindable checker with concise but high-signal-coverage properties

module tmu2_burst_sva #(
  parameter fml_depth = 26
)(
  input logic                      sys_clk,
  input logic                      sys_rst,

  // DUT ports
  input logic                      flush,
  input logic                      busy,
  input logic                      pipe_stb_i,
  input logic                      pipe_ack_o,
  input logic                      pipe_stb_o,
  input logic                      pipe_ack_i,
  input logic [15:0]               color,
  input logic [fml_depth-2:0]      dadr,
  input logic [fml_depth-6:0]      burst_addr,
  input logic [15:0]               burst_sel,
  input logic [255:0]              burst_do,

  // DUT internals we want to check
  input logic                      state,
  input logic                      next_state,
  input logic                      burst_hit,
  input logic                      empty,
  input logic                      write_en,
  input logic                      clear_en,
  input logic                      use_memorized,
  input logic [15:0]               color_r,
  input logic [fml_depth-2:0]      dadr_r,
  input logic [15:0]               color_mux,
  input logic [fml_depth-2:0]      dadr_mux
);

  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (sys_rst);

  // Basic interface/STATE invariants
  assert property ( (state==1'b0) |-> (pipe_ack_o == (~flush | empty)) );
  assert property ( (state==1'b1) |-> (pipe_ack_o == 1'b0) );
  assert property ( (state==1'b0) |-> (!pipe_stb_o && !use_memorized && !busy) );
  assert property ( (state==1'b1) |-> ( pipe_stb_o &&  use_memorized &&  busy) );

  // State transitions and control enables
  assert property ( (state==1'b0 && flush && !empty) |-> (!write_en && next_state==1'b1) );
  assert property ( (state==1'b0 && pipe_stb_i && pipe_ack_o && (burst_hit || empty))
                   |-> (write_en && next_state==1'b0) );
  assert property ( (state==1'b0 && pipe_stb_i && !burst_hit && !empty && !flush)
                   |-> (pipe_ack_o && !write_en && next_state==1'b1) );
  assert property ( (state==1'b1 &&  pipe_ack_i) |-> (clear_en && write_en && next_state==1'b0) );
  assert property ( (state==1'b1 && !pipe_ack_i) |-> (!clear_en && !write_en && next_state==1'b1) );

  // Handshake-driven capture
  assert property ( $past(pipe_stb_i && pipe_ack_o) |-> (color_r == $past(color) && dadr_r == $past(dadr)) );
  assert property ( !$past(pipe_stb_i && pipe_ack_o) |-> ($stable(color_r) && $stable(dadr_r)) );

  // Derived wires correctness
  assert property ( burst_hit == (dadr[fml_depth-2:4] == burst_addr) );
  assert property ( empty == (burst_sel == 16'd0) );

  // Write side-effects (use $past to avoid sampling races with synchronous blocking assigns)
  // Address update on write
  assert property ( $past(write_en) |-> (burst_addr == $past(dadr_mux[fml_depth-2:4])) );

  // Select bit set on write
  assert property ( $past(write_en) |-> (burst_sel[15 - $past(dadr_mux[3:0])] == 1'b1) );

  // If clear and write same cycle, select becomes exactly one-hot of current nibble
  assert property ( $past(clear_en && write_en)
                    |-> (burst_sel == (16'h8000 >> $past(dadr_mux[3:0]))) );

  // If clear without write, select clears to zero
  assert property ( $past(clear_en && !write_en) |-> (burst_sel == 16'h0000) );

  // Data lane mapping: targeted lane gets color_mux
  assert property ( $past(write_en)
                    |-> (burst_do[255 - 16*$past(dadr_mux[3:0]) -: 16] == $past(color_mux)) );

  // Flush must not allow write in RUNNING
  assert property ( (state==1'b0 && flush && !empty) |-> !write_en );

  // Coverage
  cover property (state==1'b0 && pipe_stb_i && pipe_ack_o && (burst_hit || empty));
  cover property (state==1'b0 && pipe_stb_i && !burst_hit && !empty && !flush ##1 state==1'b1);
  cover property (state==1'b0 && flush && !empty ##1 state==1'b1);
  cover property (state==1'b1 && pipe_ack_i ##1 state==1'b0);
  cover property ($past(write_en) && ($past(dadr_mux[3:0])==4'd0)  && burst_sel[15]);
  cover property ($past(write_en) && ($past(dadr_mux[3:0])==4'd15) && burst_sel[0]);

endmodule

// Bind the SVA to the DUT, exposing required internals
bind tmu2_burst tmu2_burst_sva #(.fml_depth(fml_depth)) u_tmu2_burst_sva (
  .sys_clk(sys_clk),
  .sys_rst(sys_rst),
  .flush(flush),
  .busy(busy),
  .pipe_stb_i(pipe_stb_i),
  .pipe_ack_o(pipe_ack_o),
  .pipe_stb_o(pipe_stb_o),
  .pipe_ack_i(pipe_ack_i),
  .color(color),
  .dadr(dadr),
  .burst_addr(burst_addr),
  .burst_sel(burst_sel),
  .burst_do(burst_do),
  .state(state),
  .next_state(next_state),
  .burst_hit(burst_hit),
  .empty(empty),
  .write_en(write_en),
  .clear_en(clear_en),
  .use_memorized(use_memorized),
  .color_r(color_r),
  .dadr_r(dadr_r),
  .color_mux(color_mux),
  .dadr_mux(dadr_mux)
);