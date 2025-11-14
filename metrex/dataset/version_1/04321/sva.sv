// SVA for packet_transmit
// Bindable, concise, and covers priority, updates, outputs, and reset

module packet_transmit_sva (packet_transmit dut);

  // Reset behavior must drive internal regs and all outputs to 0
  a_reset_regs: assert property (@(posedge dut.clk)
    !dut.rst_n |-> (dut.pkt_buffer==8'h00 && dut.pkt_valid==1'b0 && dut.pkt_direction==1'b0));

  a_reset_outs: assert property (@(posedge dut.clk)
    !dut.rst_n |-> (dut.exe2disp_data_out==8'h00 && dut.um2npe_data_out==8'h00 &&
                    dut.disp2usermux_data_out==8'h00 &&
                    dut.exe2disp_valid_out==0 && dut.disp2exe_alf==0 &&
                    dut.um2npe_valid_out==0 && dut.um2npe_alf==0 &&
                    dut.disp2usermux_valid_out==0 && dut.usermux2disp_alf==0));

  default clocking cb @ (posedge dut.clk); endclocking
  default disable iff (!dut.rst_n)

  // Handy selectors (respecting priority)
  let exe_sel  = dut.exe2disp_data_wr && dut.exe2disp_direction_req;
  let um_sel   = (!exe_sel) && dut.um2npe_data_wr;
  let disp_sel = (!exe_sel) && (!dut.um2npe_data_wr) && dut.disp2usermux_data_wr;
  let no_sel   = !(exe_sel || dut.um2npe_data_wr || dut.disp2usermux_data_wr);

  // Combinational data outputs always mirror buffer
  a_data_out_eq_buf: assert property (
    dut.exe2disp_data_out==dut.pkt_buffer &&
    dut.um2npe_data_out  ==dut.pkt_buffer &&
    dut.disp2usermux_data_out==dut.pkt_buffer);

  // Valid/ALF mapping by direction
  a_dir0_map: assert property (dut.pkt_direction==1'b0 |->
    (dut.disp2usermux_valid_out==0 && dut.usermux2disp_alf==0) &&
    (dut.exe2disp_valid_out==dut.pkt_valid) &&
    (dut.disp2exe_alf      ==dut.pkt_valid) &&
    (dut.um2npe_valid_out  ==dut.pkt_valid) &&
    (dut.um2npe_alf        ==dut.pkt_valid));

  a_dir1_map: assert property (dut.pkt_direction==1'b1 |->
    (dut.exe2disp_valid_out==0 && dut.disp2exe_alf==0 &&
     dut.um2npe_valid_out==0   && dut.um2npe_alf==0) &&
    (dut.disp2usermux_valid_out==dut.pkt_valid) &&
    (dut.usermux2disp_alf      ==dut.pkt_valid));

  // Redundancy checks on duplicated paths when dir==0
  a_equal_dir0_paths: assert property (
    dut.exe2disp_valid_out==dut.um2npe_valid_out &&
    dut.disp2exe_alf      ==dut.um2npe_alf);

  // Register update semantics with priority
  a_exe_update:  assert property (exe_sel |=> (
    dut.pkt_buffer   == $past(dut.exe2disp_data)     &&
    dut.pkt_valid    == $past(dut.exe2disp_valid)    &&
    dut.pkt_direction== $past(dut.exe2disp_direction)));

  a_um_update:   assert property (um_sel |=> (
    dut.pkt_buffer   == $past(dut.um2npe_data) &&
    dut.pkt_valid    == $past(dut.um2npe_valid) &&
    dut.pkt_direction== 1'b0));

  a_disp_update: assert property (disp_sel |=> (
    dut.pkt_buffer   == $past(dut.disp2usermux_data) &&
    dut.pkt_valid    == $past(dut.disp2usermux_valid) &&
    dut.pkt_direction== 1'b1));

  // No selection -> registers hold
  a_hold_when_no_sel: assert property (no_sel |=> (
    $stable(dut.pkt_buffer) && $stable(dut.pkt_valid) && $stable(dut.pkt_direction)));

  // Explicit priority checks
  a_prio_exe_over_others: assert property (
    exe_sel && (dut.um2npe_data_wr || dut.disp2usermux_data_wr) |=> (
      dut.pkt_buffer==$past(dut.exe2disp_data) &&
      dut.pkt_direction==$past(dut.exe2disp_direction)));

  a_prio_um_over_disp: assert property (
    (!exe_sel) && dut.um2npe_data_wr && dut.disp2usermux_data_wr |=> (
      dut.pkt_buffer==$past(dut.um2npe_data) && dut.pkt_direction==1'b0));

  // Functional coverage
  c_exe_path:  cover property (exe_sel);
  c_um_path:   cover property (um_sel);
  c_disp_path: cover property (disp_sel);
  c_hold:      cover property (no_sel [*2]);

  c_prio_exe_um:   cover property (exe_sel && dut.um2npe_data_wr);
  c_prio_exe_disp: cover property (exe_sel && dut.disp2usermux_data_wr);
  c_prio_um_disp:  cover property ((!exe_sel) && dut.um2npe_data_wr && dut.disp2usermux_data_wr);

  c_dir0_to_dir1: cover property (dut.pkt_valid && dut.pkt_direction==0 ##1 dut.pkt_valid && dut.pkt_direction==1);
  c_dir1_to_dir0: cover property (dut.pkt_valid && dut.pkt_direction==1 ##1 dut.pkt_valid && dut.pkt_direction==0);

  c_reset_to_first_sel: cover property (!dut.rst_n ##1 dut.rst_n ##[1:20] (exe_sel || um_sel || disp_sel));

endmodule

bind packet_transmit packet_transmit_sva sva_inst();