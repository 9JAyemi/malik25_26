// SVA for ledtest_pio_1: concise, high-quality checks and coverage

module ledtest_pio_1_sva (
  input logic         clk,
  input logic         reset_n,
  input logic  [1:0]  address,
  input logic         in_port,
  input logic [31:0]  readdata,
  input logic         clk_en,
  input logic         data_in,
  input logic         read_mux_out
);

  default clocking cb @(posedge clk); endclocking

  // Basic X checks
  assert property (cb !$isunknown({address, in_port})) else $error("X/Z on inputs");
  assert property (cb !$isunknown(readdata)) else $error("X/Z on readdata");

  // Clock enable is constant 1
  assert property (cb clk_en);

  // Combinational aliases
  assert property (cb data_in == in_port);
  assert property (cb read_mux_out == (in_port & (address == 2'b00)));

  // Functional register behavior (outside reset)
  default disable iff (!reset_n)
    assert property (cb readdata == {31'b0, (in_port & (address == 2'b00))});

  // High bits are always zero when not in reset
  default disable iff (!reset_n)
    assert property (cb readdata[31:1] == '0);

  // Asynchronous reset behavior
  assert property (@(negedge reset_n) readdata == 32'b0);
  assert property (cb (!reset_n) |-> (readdata == 32'b0));

  // Coverage
  default disable iff (!reset_n)
    cover property (cb (address == 2'b00) && in_port ##1 (readdata == 32'h1));
  default disable iff (!reset_n)
    cover property (cb (address != 2'b00) ##1 (readdata == 32'h0));
  default disable iff (!reset_n)
    cover property (cb $rose(in_port) && (address == 2'b00) ##1 readdata[0]);
  default disable iff (!reset_n)
    cover property (cb $fell(in_port) && (address == 2'b00) ##1 !readdata[0]);
  // Hit all address values
  default disable iff (!reset_n)
    cover property (cb $changed(address));
endmodule

bind ledtest_pio_1 ledtest_pio_1_sva u_sva (
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .readdata(readdata),
  .clk_en(clk_en),
  .data_in(data_in),
  .read_mux_out(read_mux_out)
);