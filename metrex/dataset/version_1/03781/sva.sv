// SVA checker for wasca_external_sdram_controller_input_efifo_module (2-entry FIFO)
module wasca_external_sdram_controller_input_efifo_module_sva
(
  input  logic         clk,
  input  logic         reset_n,

  // DUT inputs/outputs
  input  logic         rd,
  input  logic         wr,
  input  logic [42:0]  wr_data,
  input  logic [42:0]  rd_data,
  input  logic         full,
  input  logic         empty,
  input  logic         almost_full,
  input  logic         almost_empty,

  // DUT internal state
  input  logic [1:0]   entries,
  input  logic         rd_address,
  input  logic         wr_address,
  input  logic [42:0]  entry_0,
  input  logic [42:0]  entry_1,
  input  logic [1:0]   rdwr
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Async reset effect observed on clock edge
  property p_async_reset;
    @(posedge clk) !reset_n |-> (entries==2'd0 && wr_address==1'b0 && rd_address==1'b0);
  endproperty
  assert property (p_async_reset);

  // Legal range and flags correctness
  assert property (entries inside {[2'd0:2'd2]});
  assert property (full         == (entries==2'd2));
  assert property (empty        == (entries==2'd0));
  assert property (almost_full  == (entries>=2'd1));
  assert property (almost_empty == (entries<=2'd1));
  assert property (!(full && empty));

  // No-op cycle
  assert property ((rdwr==2'b00) |=> $stable(entries) && $stable(wr_address) && $stable(rd_address));

  // Write-only cycle
  assert property ((rdwr==2'b01 && !full) |=> entries == $past(entries)+2'd1
                                          && wr_address == ~$past(wr_address)
                                          && $stable(rd_address));
  assert property ((rdwr==2'b01 &&  full) |=> $stable(entries) && $stable(wr_address) && $stable(rd_address)
                                          && $stable(entry_0) && $stable(entry_1));

  // Read-only cycle
  assert property ((rdwr==2'b10 && !empty) |=> entries == $past(entries)-2'd1
                                           && rd_address == ~$past(rd_address)
                                           && $stable(wr_address));
  assert property ((rdwr==2'b10 &&  empty) |=> $stable(entries) && $stable(wr_address) && $stable(rd_address));

  // Simultaneous read & write
  assert property ((rdwr==2'b11) |=> entries == $past(entries)
                                   && rd_address == ~$past(rd_address)
                                   && wr_address == ~$past(wr_address));

  // Combinational read data routing
  assert property (rd_data == (rd_address ? entry_1 : entry_0));

  // Write actually stores into the targeted entry when allowed
  assert property ((wr && !full && (wr_address==1'b0)) |=> entry_0 == $past(wr_data));
  assert property ((wr && !full && (wr_address==1'b1)) |=> entry_1 == $past(wr_data));

  // Minimal FIFO ordering check (two pushes then two pops, no interleaving)
  property p_order_two_deep;
    logic [42:0] d0, d1;
    (wr && !full, d0 = wr_data)
    ##1 (!rd && wr && !full, d1 = wr_data)
    ##1 (!wr && rd && !empty && rd_data==d0)
    ##1 (!wr && rd && !empty && rd_data==d1);
  endproperty
  assert property (p_order_two_deep);

  // Coverage
  cover property (entries==2'd0 ##1 wr && !full ##1 wr && !full ##1 entries==2'd2);           // fill to full
  cover property (entries==2'd2 ##1 rd && !empty ##1 rd && !empty ##1 entries==2'd0);          // drain to empty
  cover property (rd && wr);                                                                     // simultaneous R/W
  cover property (full  && wr && !rd);                                                           // blocked write
  cover property (empty && rd && !wr);                                                           // blocked read
  cover property (wr && !full ##1 wr && !full && wr_address == $past(wr_address,2));            // wr ptr wrap
  cover property (rd && !empty ##1 rd && !empty && rd_address == $past(rd_address,2));          // rd ptr wrap

endmodule

// Example bind (connects to internal regs/wires by name)
bind wasca_external_sdram_controller_input_efifo_module
  wasca_external_sdram_controller_input_efifo_module_sva sva_i (
    .clk        (clk),
    .reset_n    (reset_n),
    .rd         (rd),
    .wr         (wr),
    .wr_data    (wr_data),
    .rd_data    (rd_data),
    .full       (full),
    .empty      (empty),
    .almost_full(almost_full),
    .almost_empty(almost_empty),
    .entries    (entries),
    .rd_address (rd_address),
    .wr_address (wr_address),
    .entry_0    (entry_0),
    .entry_1    (entry_1),
    .rdwr       (rdwr)
  );