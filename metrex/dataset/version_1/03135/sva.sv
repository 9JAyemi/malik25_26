// SVA for dual_port_RAM
// Bind this SVA to the DUT; it references internal 'mem' directly.

module dual_port_RAM_sva;
  default clocking cb @(posedge clk); endclocking

  // Controls/addresses must be known when used and in range (0..7)
  assert property (disable iff (!rst_n) read_en  |-> (read_addr[7:3]==0) && !$isunknown(read_addr));
  assert property (disable iff (!rst_n) write_en |-> (write_addr[7:3]==0) && !$isunknown(write_addr) && !$isunknown(write_data));
  assert property (!$isunknown({rst_n,read_en,write_en}));

  // Reset: read_data forced to 0 whenever reset is low (checked on clocks)
  assert property (!rst_n |-> read_data==4'h0);

  // When not reading, read_data holds its value
  assert property (disable iff (!rst_n) $past(rst_n) && !read_en |-> read_data==$past(read_data));

  // Read returns the stored value from the prior cycle (read-before-write semantics)
  assert property (disable iff (!rst_n) read_en |-> read_data==$past(mem[$past(read_addr)]));

  // Writes: targeted entry updates; all non-target entries remain unchanged
  genvar i;
  generate
    for (i=0; i<8; i++) begin : G
      assert property (disable iff (!rst_n)
        $past(write_en) && $past(write_addr[7:3]==0) && $past(write_addr)==i
        |-> mem[i]==$past(write_data));
      assert property (disable iff (!rst_n)
        $past(write_en) && $past(write_addr[7:3]==0) && $past(write_addr)!=i
        |-> mem[i]==$past(mem[i]));
    end
  endgenerate

  // Coverage
  cover property ($rose(rst_n));
  cover property (write_en && write_addr[7:3]==0);
  cover property (read_en  && read_addr[7:3]==0);
  cover property (write_en && write_addr[7:3]==0 ##1 read_en && read_addr==$past(write_addr) && read_data==$past(write_data));
  cover property (read_en && write_en && (read_addr==write_addr)); // same-cycle R/W, same addr
endmodule

bind dual_port_RAM dual_port_RAM_sva sva();