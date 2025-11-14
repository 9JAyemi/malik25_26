// SVA for module memory. Bind this checker to the DUT.

module memory_sva #(parameter int unsigned BASE_ADDRESS = 25'd0)
(
  input  logic        clk,
  input  logic        mem_read,
  input  logic        mem_write,
  input  logic [31:0] address,
  input  logic [31:0] data_in,
  input  logic [31:0] data_out,
  input  logic [4:0]  mem_offset,
  input  logic        address_select,
  input  logic [31:0] mem_array [0:31]
);

  // Internal signal equivalence
  assert property (@(posedge clk) address_select == (address[31:7] == BASE_ADDRESS));
  assert property (@(posedge clk) mem_offset == address[6:2]);

  // Alignment required on selected accesses
  assert property (@(posedge clk) (mem_read || mem_write) && address_select |-> address[1:0] == 2'b00);

  // Read behavior
  assert property (@(posedge clk) mem_read && address_select |-> data_out == mem_array[mem_offset]);

  // Not a selected read => data_out must be unknown (X)
  assert property (@(posedge clk) !(mem_read && address_select) |-> $isunknown(data_out));

  // Write takes effect next cycle at the written offset
  assert property (@(posedge clk) mem_write && address_select
                   |=> mem_array[$past(mem_offset)] == $past(data_in));

  // No unintended writes: any entry change implies a qualifying write to that entry
  genvar k;
  generate
    for (k = 0; k < 32; k++) begin : g_no_spurious_writes
      assert property (@(posedge clk)
                       mem_array[k] != $past(mem_array[k])
                       |-> $past(mem_write && address_select && (mem_offset == k)));
    end
  endgenerate

  // Power-up/init contents
  generate
    for (k = 0; k < 32; k++) begin : g_init_contents
      assert property ($initstate |-> mem_array[k] == (k*4));
    end
  endgenerate

  // Coverage
  cover property (@(posedge clk) mem_write && address_select);
  cover property (@(posedge clk) mem_read  && address_select);
  cover property (@(posedge clk) mem_read && mem_write && address_select); // simultaneous R/W
  cover property (@(posedge clk) mem_write && address_select && mem_offset ==  0);
  cover property (@(posedge clk) mem_write && address_select && mem_offset == 31);
  cover property (@(posedge clk) mem_read  && address_select && mem_offset ==  0);
  cover property (@(posedge clk) mem_read  && address_select && mem_offset == 31);
  cover property (@(posedge clk) mem_write && address_select ##1
                               mem_read  && address_select && $stable(mem_offset)); // RAW same addr
  cover property (@(posedge clk) !(mem_read && address_select) && $isunknown(data_out));

endmodule

bind memory memory_sva #(.BASE_ADDRESS(BASE_ADDRESS)) u_memory_sva (
  .clk(clk),
  .mem_read(mem_read),
  .mem_write(mem_write),
  .address(address),
  .data_in(data_in),
  .data_out(data_out),
  .mem_offset(mem_offset),
  .address_select(address_select),
  .mem_array(mem_array)
);