// SVA for jaxa_errorStatus
module jaxa_errorStatus_sva (
  input logic         clk,
  input logic         reset_n,
  input logic  [1:0]  address,
  input logic  [7:0]  in_port,
  input logic [31:0]  readdata,
  input logic  [7:0]  read_mux_out,
  input logic         clk_en
);
  default clocking cb @(posedge clk); endclocking

  // Basic invariants
  assert property (@(posedge clk) !reset_n |-> readdata == 32'h0);
  assert property (@(negedge reset_n) readdata == 32'h0);
  assert property (@(posedge clk) readdata[31:8] == 24'h0);
  assert property (@(posedge clk) clk_en == 1'b1);

  // Combinational decode correctness
  assert property (@(posedge clk) read_mux_out == ((address==2'b00) ? in_port : 8'h00));

  // Sequential update: first active cycle after reset release
  assert property (@(posedge clk)
    $rose(reset_n) |-> readdata == {24'h0, ((address==2'b00) ? in_port : 8'h00)}
  );

  // Sequential update: steady-state cycles
  assert property (@(posedge clk)
    reset_n && $past(reset_n) |-> readdata == $past({24'h0, ((address==2'b00) ? in_port : 8'h00)})
  );

  // Functional covers
  cover property (@(posedge clk) $rose(reset_n));
  cover property (@(posedge clk) reset_n && address==2'b00 && in_port!=8'h00 ##1 readdata[7:0]==$past(in_port));
  cover property (@(posedge clk) reset_n && address!=2'b00 ##1 readdata==32'h0);
endmodule

bind jaxa_errorStatus jaxa_errorStatus_sva sva (
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .readdata(readdata),
  .read_mux_out(read_mux_out),
  .clk_en(clk_en)
);