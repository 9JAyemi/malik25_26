// SVA for RegisterFile
// Bind this checker to the DUT
module RegisterFile_sva (
  input  logic        clk,
  input  logic [1:0]  io_rs1_thread,
  input  logic [4:0]  io_rs1_addr,
  input  logic [31:0] io_rs1_data,
  input  logic [1:0]  io_rs2_thread,
  input  logic [4:0]  io_rs2_addr,
  input  logic [31:0] io_rs2_data,
  input  logic [1:0]  io_rd_thread,
  input  logic [4:0]  io_rd_addr,
  input  logic [31:0] io_rd_data,
  input  logic        io_rd_enable,
  ref    logic [31:0] regfile [127:0]
);

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Reads: next-cycle output equals prior-cycle regfile at {addr,thread}, or zero for x0
  assert property ( 1'b1 |=> io_rs1_data ==
                    (( $past(io_rs1_addr)==5'h0 ) ? 32'h0
                     : $past(regfile[{ $past(io_rs1_addr), $past(io_rs1_thread)}])) );

  assert property ( 1'b1 |=> io_rs2_data ==
                    (( $past(io_rs2_addr)==5'h0 ) ? 32'h0
                     : $past(regfile[{ $past(io_rs2_addr), $past(io_rs2_thread)}])) );

  // Write: regfile[{addr,thread}] updated on enable
  assert property ( $past(io_rd_enable)
                    |=> regfile[{ $past(io_rd_addr), $past(io_rd_thread)}] == $past(io_rd_data) );

  // Threads 0/1/2: both the concatenated index and the linear (addr + 32*thread) get the same data
  assert property (
    $past(io_rd_enable) && ($past(io_rd_thread) inside {2'b00,2'b01,2'b10})
    |=> ( regfile[{ $past(io_rd_addr), $past(io_rd_thread)}] == $past(io_rd_data)
       && regfile[$unsigned($past(io_rd_addr)) + ($unsigned($past(io_rd_thread))<<5)] == $past(io_rd_data)
       && regfile[{ $past(io_rd_addr), $past(io_rd_thread)}]
          == regfile[$unsigned($past(io_rd_addr)) + ($unsigned($past(io_rd_thread))<<5)] )
  );

  // Two read ports select same nonzero index => next-cycle outputs match
  assert property (
    ($past({io_rs1_addr,io_rs1_thread}) == $past({io_rs2_addr,io_rs2_thread}))
    && ($past(io_rs1_addr)!=5'h0) && ($past(io_rs2_addr)!=5'h0)
    |=> (io_rs1_data == io_rs2_data)
  );

  // Coverage
  cover property ( $past(io_rs1_addr)==5'h0 |=> io_rs1_data==32'h0 );
  cover property ( $past(io_rs2_addr)==5'h0 |=> io_rs2_data==32'h0 );
  cover property ( $past(io_rd_enable) && ($past(io_rd_thread) inside {2'b00,2'b01,2'b10}) );
  cover property ( $past(io_rd_enable) && $past(io_rd_thread)==2'b11 );
  cover property ( ($past({io_rs1_addr,io_rs1_thread}) == $past({io_rd_addr,io_rd_thread}))
                   && ($past(io_rs1_addr)!=5'h0) );
  cover property ( ($past({io_rs1_addr,io_rs1_thread}) == $past({io_rs2_addr,io_rs2_thread}))
                   && ($past(io_rs1_addr)!=5'h0) );

endmodule

bind RegisterFile RegisterFile_sva rf_sva (
  .clk(clk),
  .io_rs1_thread(io_rs1_thread),
  .io_rs1_addr(io_rs1_addr),
  .io_rs1_data(io_rs1_data),
  .io_rs2_thread(io_rs2_thread),
  .io_rs2_addr(io_rs2_addr),
  .io_rs2_data(io_rs2_data),
  .io_rd_thread(io_rd_thread),
  .io_rd_addr(io_rd_addr),
  .io_rd_data(io_rd_data),
  .io_rd_enable(io_rd_enable),
  .regfile(regfile)
);