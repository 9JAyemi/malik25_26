// SVA for nios_dut_pio_2
module nios_dut_pio_2_sva (
  input        clk,
  input        reset_n,
  input  [1:0] address,
  input [19:0] in_port,
  input [31:0] readdata,
  input [19:0] data_in,
  input [19:0] read_mux_out,
  input        clk_en
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity/known checks
  assert property ( !$isunknown(reset_n) );
  assert property ( !$isunknown(address) );
  assert property ( !$isunknown(in_port) );
  assert property ( disable iff (!reset_n) !$isunknown(readdata) );

  // Static nets/comb
  assert property ( clk_en == 1'b1 );
  assert property ( data_in == in_port );

  // Decode correctness for read_mux_out
  assert property ( (address == 2'b00) |-> (read_mux_out == data_in) );
  assert property ( (address == 2'b01) |-> (read_mux_out == in_port) );
  assert property ( (address inside {2'b10,2'b11}) |-> (read_mux_out == 20'h0) );

  // Register update and zero-extension behavior
  assert property ( readdata[31:20] == 12'h0 );
  assert property ( disable iff (!reset_n)
                    readdata[19:0] == $past(read_mux_out, 1, !reset_n) );

  // End-to-end: output matches selected input on next cycle
  assert property ( disable iff (!reset_n)
                    $past(address inside {2'b00,2'b01}, 1, !reset_n)
                    |-> (readdata == {12'h0, $past(in_port,1,!reset_n)}) );
  assert property ( disable iff (!reset_n)
                    $past(address inside {2'b10,2'b11}, 1, !reset_n)
                    |-> (readdata == 32'h0) );

  // Reset behavior: while reset asserted, output held at zero
  assert property ( !reset_n |-> (readdata == 32'h0) );

  // Coverage
  cover property ( !reset_n ##1 reset_n );
  cover property ( address == 2'b00 );
  cover property ( address == 2'b01 );
  cover property ( address == 2'b10 );
  cover property ( address == 2'b11 );
  cover property ( disable iff (!reset_n)
                   (address inside {2'b00,2'b01} && $changed(in_port))
                   ##1 (readdata[19:0] == $past(in_port)) );

endmodule

bind nios_dut_pio_2 nios_dut_pio_2_sva sva_i (
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .readdata(readdata),
  .data_in(data_in),
  .read_mux_out(read_mux_out),
  .clk_en(clk_en)
);