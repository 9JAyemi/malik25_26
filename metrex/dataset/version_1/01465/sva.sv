// SVA for dff_ram and xor_ram
// Concise, high-value checks + coverage

// ---------------- dff_ram SVA ----------------
module dff_ram_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        we,
  input  logic        re,
  input  logic [7:0]  waddr,
  input  logic [7:0]  raddr,
  input  logic [3:0]  d,
  output logic [3:0]  q,
  input  logic [3:0]  ram [0:7],
  input  logic [2:0]  read_ptr,
  input  logic [2:0]  write_ptr,
  input  logic [2:0]  next_write_ptr
);

  default clocking cb @(posedge clk); endclocking

  // Async reset takes effect immediately
  property p_async_reset;
    @(negedge rst_n) 1 |-> (q==4'b0 && read_ptr==3'b0 && write_ptr==3'b0 && next_write_ptr==3'b0);
  endproperty
  assert property (p_async_reset);

  // Address range and knownness when used
  assert property (disable iff (!rst_n) we |-> (waddr[7:3]==5'b0 && !$isunknown({waddr[2:0], d})));
  assert property (disable iff (!rst_n) re |-> (raddr[7:3]==5'b0 && !$isunknown(raddr[2:0])));

  // No X on q during normal operation
  assert property (disable iff (!rst_n) !$isunknown(q));

  // Write effect on RAM contents
  assert property (disable iff (!rst_n) we |=> ram[$past(waddr[2:0])] == $past(d));

  // Pointer relations
  assert property (disable iff (!rst_n) we  |=> next_write_ptr == $past(write_ptr) + 3'd1);
  assert property (disable iff (!rst_n) !we |=> $stable(next_write_ptr));
  assert property (disable iff (!rst_n) 1   |=> write_ptr == $past(next_write_ptr));

  // Read behavior: q XOR with old RAM data; q holds when no read
  assert property (disable iff (!rst_n) re  |=> q == ($past(q) ^ $past(ram[$past(raddr[2:0])])));
  assert property (disable iff (!rst_n) !re |=> $stable(q));

  // read_ptr increments iff re
  assert property (disable iff (!rst_n) re  |=> read_ptr == $past(read_ptr) + 3'd1);
  assert property (disable iff (!rst_n) !re |=> $stable(read_ptr));

  // Coverage
  cover property (disable iff (!rst_n) we);
  cover property (disable iff (!rst_n) re);
  cover property (disable iff (!rst_n) we && re);
  cover property (disable iff (!rst_n) we && (waddr[2:0]==3'd0));
  cover property (disable iff (!rst_n) we && (waddr[2:0]==3'd7));
  cover property (disable iff (!rst_n) re && (raddr[2:0]==3'd0));
  cover property (disable iff (!rst_n) re && (raddr[2:0]==3'd7));
  cover property (disable iff (!rst_n) (write_ptr==3'd7 && we) |=> (next_write_ptr==3'd0));

endmodule

bind dff_ram dff_ram_sva
(
  .clk(clk),
  .rst_n(rst_n),
  .we(we),
  .re(re),
  .waddr(waddr),
  .raddr(raddr),
  .d(d),
  .q(q),
  .ram(ram),
  .read_ptr(read_ptr),
  .write_ptr(write_ptr),
  .next_write_ptr(next_write_ptr)
);

// ---------------- xor_ram SVA ----------------
module xor_ram_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [7:0]  write_addr,
  input  logic [3:0]  write_data,
  input  logic        read_en,
  input  logic [7:0]  read_addr,
  input  logic [7:0]  final_output,
  input  logic [3:0]  dff_data,
  input  logic [3:0]  ram_data
);

  default clocking cb @(posedge clk); endclocking

  // Async reset effect
  assert property (@(negedge rst_n) 1 |-> final_output==8'b0);

  // Tied-off write enable on the RAM instance
  assert property (disable iff (!rst_n) dff_ram_inst.we == 1'b1);

  // Address range constraints at top-level
  assert property (disable iff (!rst_n) write_addr[7:3]==5'b0);
  assert property (disable iff (!rst_n) read_en |-> (read_addr[7:3]==5'b0 && !$isunknown(read_addr[2:0])));

  // Datapath timing
  assert property (disable iff (!rst_n) 1 |=> dff_data == $past(write_data));
  assert property (disable iff (!rst_n) 1 |=> final_output == {$past(ram_data), $past(dff_data)});
  assert property (disable iff (!rst_n) !$isunknown(final_output));

  // Coverage
  cover property (disable iff (!rst_n) read_en);
  cover property (disable iff (!rst_n) final_output != $past(final_output));

endmodule

bind xor_ram xor_ram_sva
(
  .clk(clk),
  .rst_n(rst_n),
  .write_addr(write_addr),
  .write_data(write_data),
  .read_en(read_en),
  .read_addr(read_addr),
  .final_output(final_output),
  .dff_data(dff_data),
  .ram_data(ram_data)
);