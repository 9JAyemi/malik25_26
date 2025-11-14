// Bind these SVA to the DUT
bind register_file register_file_sva();

module register_file_sva;

  // Inserted in the DUT scope by bind; can see clk, registers, etc.
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid)

  // Write updates exactly one register; others hold. Also no-change when !write_en.
  genvar i;
  generate
    for (i=0; i<8; i++) begin : G_WRITE_CHECKS
      assert property (write_en |-> ##1
                       (i == $past(write_reg) ? registers[i] == $past(write_data)
                                              : registers[i] == $past(registers[i])));
      assert property (!write_en |-> $stable(registers[i]));

      // Coverage per address
      cover property (write_en && write_reg == i);
      cover property (read_en && read_reg1 == i);
      cover property (read_en && read_reg2 == i);
    end
  endgenerate

  // Read ports return the pre-state array contents (old data) on reads.
  assert property (read_en |-> ##1 read_data1 == $past(registers[$past(read_reg1)]));
  assert property (read_en |-> ##1 read_data2 == $past(registers[$past(read_reg2)]));

  // Outputs hold when not reading.
  assert property (!read_en |-> $stable(read_data1) && $stable(read_data2));

  // If both ports read same address, results must match.
  assert property (read_en && (read_reg1 == read_reg2) |-> ##1 read_data1 == read_data2);

  // Key functional coverage
  cover property (write_en && read_en); // concurrent read/write
  cover property (write_en && read_en && (read_reg1 == write_reg)); // RAW hazard (port1)
  cover property (write_en && read_en && (read_reg2 == write_reg)); // RAW hazard (port2)
  cover property (read_en && (read_reg1 != read_reg2)); // dual-read different regs
  cover property (read_en && (read_reg1 == read_reg2)); // dual-read same reg
  cover property (write_en ##1 (write_en && (write_reg == $past(write_reg)))); // back-to-back same reg write
  cover property (write_en ##1 (read_en && (read_reg1 == $past(write_reg)))); // write then read-back (port1)
  cover property (write_en ##1 (read_en && (read_reg2 == $past(write_reg)))); // write then read-back (port2)

endmodule