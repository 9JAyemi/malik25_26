// Assertions for drac_wb_adapter
// Bind this module to the DUT
bind drac_wb_adapter drac_wb_adapter_sva sva_inst();

module drac_wb_adapter_sva;

  // Short-hands
  let new_req = wb_stb_i && !wb_stb_delay;   // rising-edge detect
  let busy    = read || write;

  // --------------------------------------------
  // Basic protocol and gating on clk75
  // --------------------------------------------
  // wb_stb_delay must mirror previous wb_stb_i
  assert property (@(posedge clk75) disable iff (reset)
    wb_stb_delay == $past(wb_stb_i));

  // Only one of read/write can be 1
  assert property (@(posedge clk75) disable iff (reset)
    !(read && write));
  assert property (@(posedge clk75) disable iff (reset)
    !(drac_srd_o && drac_swr_o));

  // read/write only start on new_req with correct we decode
  assert property (@(posedge clk75) disable iff (reset)
    $rose(read)  |-> $past(new_req && !wb_we_i));
  assert property (@(posedge clk75) disable iff (reset)
    $rose(write) |-> $past(new_req &&  wb_we_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req |=> (read == !wb_we_i) && (write == wb_we_i));

  // No overlapping requests while a transaction is outstanding
  assert property (@(posedge clk75) disable iff (reset)
    busy |-> !new_req);

  // Once asserted, read/write stay asserted until rdy1 (request holds until completion)
  assert property (@(posedge clk75) disable iff (reset)
    $rose(read)  |-> (read  until_with rdy1));
  assert property (@(posedge clk75) disable iff (reset)
    $rose(write) |-> (write until_with rdy1));

  // On rdy1, read/write must drop next cycle
  assert property (@(posedge clk75) disable iff (reset)
    rdy1 |=> !read && !write);

  // --------------------------------------------
  // ACK behavior on clk75
  // --------------------------------------------
  // ack only when rdy1 is seen; ack is never high for two consecutive cycles
  assert property (@(posedge clk75) disable iff (reset)
    wb_ack_o |-> rdy1);
  assert property (@(posedge clk75) disable iff (reset)
    wb_ack_o |=> !wb_ack_o);

  // ack implies there was an outstanding request in the previous cycle
  assert property (@(posedge clk75) disable iff (reset)
    wb_ack_o |-> $past(busy));

  // --------------------------------------------
  // Address capture and stability (clk75)
  // --------------------------------------------
  // Capture addr and exported drac_sa_o on new request
  assert property (@(posedge clk75) disable iff (reset)
    new_req |=> (addr[33:2] == $past(wb_adr_i[31:0])) && (drac_sa_o == $past(wb_adr_i[31:3])));

  // Address must remain stable while transaction outstanding
  assert property (@(posedge clk75) disable iff (reset)
    busy && !rdy1 |-> $stable(addr[33:2]));

  // --------------------------------------------
  // Write data and mask mapping (clk75)
  // --------------------------------------------
  // Mask decode
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b000) |=> msk == 32'hFFFFFFF0);
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b001) |=> msk == 32'hFFFFFF0F);
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b010) |=> msk == 32'hFFFFF0FF);
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b011) |=> msk == 32'hFFFF0FFF);
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b100) |=> msk == 32'hFFF0FFFF);
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b101) |=> msk == 32'hFF0FFFFF);
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b110) |=> msk == 32'hF0FFFFFF);
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b111) |=> msk == 32'h0FFFFFFF);

  // Write data lane captured correctly into 256b line
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b000) |=> drac_swdat_o[ 31:  0] == $past(wb_dat_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b001) |=> drac_swdat_o[ 63: 32] == $past(wb_dat_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b010) |=> drac_swdat_o[ 95: 64] == $past(wb_dat_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b011) |=> drac_swdat_o[127: 96] == $past(wb_dat_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b100) |=> drac_swdat_o[159:128] == $past(wb_dat_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b101) |=> drac_swdat_o[191:160] == $past(wb_dat_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b110) |=> drac_swdat_o[223:192] == $past(wb_dat_i));
  assert property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0]==3'b111) |=> drac_swdat_o[255:224] == $past(wb_dat_i));

  // --------------------------------------------
  // Read data return mapping (clk150)
  // --------------------------------------------
  // rdy1 set only by drac_srdy_i (unless cleared same cycle by rdy2)
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && !rdy2 |=> rdy1);

  // rdat mux is correct on drac_srdy_i
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b000) |=> rdat == drac_srdat_i[ 31:  0]);
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b001) |=> rdat == drac_srdat_i[ 63: 32]);
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b010) |=> rdat == drac_srdat_i[ 95: 64]);
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b011) |=> rdat == drac_srdat_i[127: 96]);
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b100) |=> rdat == drac_srdat_i[159:128]);
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b101) |=> rdat == drac_srdat_i[191:160]);
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b110) |=> rdat == drac_srdat_i[223:192]);
  assert property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2]==3'b111) |=> rdat == drac_srdat_i[255:224]);

  // --------------------------------------------
  // Minimal functional coverage
  // --------------------------------------------
  // Read then ack
  cover property (@(posedge clk75) disable iff (reset)
    new_req && !wb_we_i ##[1:20] wb_ack_o);

  // Write then ack
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i ##[1:20] wb_ack_o);

  // Exercise all 8 lanes for write
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b000));
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b001));
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b010));
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b011));
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b100));
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b101));
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b110));
  cover property (@(posedge clk75) disable iff (reset)
    new_req && wb_we_i && (wb_adr_i[2:0] == 3'b111));

  // Exercise all 8 lanes for read data selection
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b000));
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b001));
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b010));
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b011));
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b100));
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b101));
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b110));
  cover property (@(posedge clk150) disable iff (reset)
    drac_srdy_i && (addr[4:2] == 3'b111));

endmodule