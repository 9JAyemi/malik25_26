// SystemVerilog Assertions for pcie_rx_recv
// Place inside the module or bind into the instance.
// These focus on FSM, straddling/ready, error semantics, enables, and datapath alignment.

// synthesis translate_off
// pragma coverage off

// Default clock/reset
default clocking cb @ (posedge pcie_user_clk); endclocking
default disable iff (!pcie_user_rst_n);

// -------------------------------
// Reset and state sanity
// -------------------------------
property p_reset_state;
  !pcie_user_rst_n |=> (cur_state == S_RX_IDLE_SOF &&
                        !r_pcie_mreq_err && !r_pcie_cpld_err && !r_pcie_cpld_len_err);
endproperty
assert property (p_reset_state);

assert property (cur_state inside {S_RX_IDLE_SOF, S_RX_DATA, S_RX_STRADDLED, S_RX_STRADDLED_HOLD});
assert property (cur_state == S_RX_STRADDLED_HOLD |=> cur_state == S_RX_IDLE_SOF);

// -------------------------------
// Ready/hold/straddle relationships
// -------------------------------
assert property (s_axis_rx_tready == ~r_rx_straddled_hold);

assert property ((cur_state == S_RX_IDLE_SOF)      |-> (!r_rx_straddled && !r_rx_straddled_hold));
assert property ((cur_state == S_RX_DATA)          |-> (!r_rx_straddled && !r_rx_straddled_hold));
assert property ((cur_state == S_RX_STRADDLED)     |-> ( r_rx_straddled && !r_rx_straddled_hold));
assert property ((cur_state == S_RX_STRADDLED_HOLD)|-> ( r_rx_straddled &&  r_rx_straddled_hold));

// Registered copy of straddle flag
assert property (r_rx_data_straddled == $past(r_rx_straddled));

// Entry/exit corner transitions
assert property ($rose(cur_state == S_RX_STRADDLED) |-> $past(cur_state == S_RX_IDLE_SOF &&
                                                               s_axis_rx_tvalid && w_rx_is_sof[4] &&
                                                               !w_rx_is_eof[4] && w_rx_is_sof[3]));
assert property ($rose(cur_state == S_RX_STRADDLED_HOLD) |-> $past(cur_state == S_RX_STRADDLED &&
                                                                    s_axis_rx_tvalid && w_rx_is_eof[4] &&
                                                                    !w_rx_is_sof[4] && w_rx_is_eof[3]));

// -------------------------------
// Type capture, header fields, and errors
// -------------------------------
property p_capture_types_and_len;
  (s_axis_rx_tvalid && w_rx_is_sof[4])
  |=> (r_pcie_mreq_type == (w_pcie_mreq_type & ~w_mreq_head_ep) &&
       r_pcie_cpld_type == (w_pcie_cpld_type & ~w_cpld_head_ep & (w_cpld_head_cs == 0)) &&
       r_cpld_len      ==  w_cpld_head_len &&
       r_cpld_bc[11:2] ==  w_cpld_head_bc[11:2]);
endproperty
assert property (p_capture_types_and_len);

// Error flag cause and stickiness
assert property ($rose(r_pcie_mreq_err) |-> $past(s_axis_rx_tvalid && w_rx_is_sof[4] &&
                                                  w_pcie_mreq_type && w_mreq_head_ep));
assert property ($rose(r_pcie_cpld_err) |-> $past(s_axis_rx_tvalid && w_rx_is_sof[4] &&
                                                  w_pcie_cpld_type &&
                                                  (w_cpld_head_ep || (w_cpld_head_cs != 0))));
assert property ($rose(r_pcie_cpld_len_err) |-> (r_pcie_cpld_type && (r_cpld_len < 2)));

assert property ((r_pcie_mreq_err      && pcie_user_rst_n) |=> r_pcie_mreq_err);
assert property ((r_pcie_cpld_err      && pcie_user_rst_n) |=> r_pcie_cpld_err);
assert property ((r_pcie_cpld_len_err  && pcie_user_rst_n) |=> r_pcie_cpld_len_err);

// -------------------------------
// Enables imply correct type and EOF/tag_last semantics
// -------------------------------
property p_mreq_en_implies_type_or_idle_pulse;
  r_mreq_fifo_wr_en
  |-> (r_pcie_mreq_type ||
       (cur_state == S_RX_IDLE_SOF && s_axis_rx_tvalid && w_rx_is_sof[4] &&
        !w_rx_is_sof[3] && w_pcie_mreq_type));
endproperty
assert property (p_mreq_en_implies_type_or_idle_pulse);

assert property (r_cpld_fifo_wr_en |-> r_pcie_cpld_type);

property p_cpld_tag_last_conditions;
  $rose(r_cpld_tag_last)
  |-> (r_pcie_cpld_type && (r_cpld_len == r_cpld_bc[11:2]) &&
       ((cur_state == S_RX_DATA       && s_axis_rx_tvalid && w_rx_is_eof[4]) ||
        (cur_state == S_RX_STRADDLED  && s_axis_rx_tvalid && w_rx_is_eof[4] && !w_rx_is_eof[3]) ||
        (cur_state == S_RX_STRADDLED_HOLD)));
endproperty
assert property (p_cpld_tag_last_conditions);

assert property ($rose(r_cpld_tag_last) |=> r_cpld_fifo_tag_last);

// -------------------------------
// Datapath alignment and byte swapping
// -------------------------------
// MREQ/cpld internal packing
assert property (!r_rx_data_straddled
                 |-> (r_mreq_fifo_wr_data == r_s_axis_rx_tdata &&
                      r_cpld_fifo_wr_data == {r_s_axis_rx_tdata[95:0], r_s_axis_rx_tdata_d1[127:96]}));
assert property ( r_rx_data_straddled
                 |-> (r_mreq_fifo_wr_data == {r_s_axis_rx_tdata[63:0],  r_s_axis_rx_tdata_d1[127:64]} &&
                      r_cpld_fifo_wr_data == {r_s_axis_rx_tdata[31:0],  r_s_axis_rx_tdata_d1[127:32]}));

// Output byte swap correctness when writing CPLD
assert property (cpld_fifo_wr_en
                 |-> (cpld_fifo_wr_data[31:0]   == {r_cpld_fifo_wr_data[7:0],   r_cpld_fifo_wr_data[15:8],
                                                     r_cpld_fifo_wr_data[23:16], r_cpld_fifo_wr_data[31:24]}     &&
                      cpld_fifo_wr_data[63:32]  == {r_cpld_fifo_wr_data[39:32], r_cpld_fifo_wr_data[47:40],
                                                     r_cpld_fifo_wr_data[55:48], r_cpld_fifo_wr_data[63:56]}     &&
                      cpld_fifo_wr_data[95:64]  == {r_cpld_fifo_wr_data[71:64], r_cpld_fifo_wr_data[79:72],
                                                     r_cpld_fifo_wr_data[87:80], r_cpld_fifo_wr_data[95:88]}     &&
                      cpld_fifo_wr_data[127:96] == {r_cpld_fifo_wr_data[103:96], r_cpld_fifo_wr_data[111:104],
                                                     r_cpld_fifo_wr_data[119:112], r_cpld_fifo_wr_data[127:120]}));

// No-X on data when writing
assert property (r_mreq_fifo_wr_en |-> !$isunknown(mreq_fifo_wr_data));
assert property (r_cpld_fifo_wr_en |-> !$isunknown(cpld_fifo_wr_data));

// -------------------------------
// Functional coverage
// -------------------------------
// Non-straddled MReq frame, multi-beat, clean EOF
cover property (pcie_user_rst_n ##1
                (cur_state==S_RX_IDLE_SOF && s_axis_rx_tvalid && w_rx_is_sof[4] &&
                 !w_rx_is_sof[3] && !w_rx_is_eof[4] && w_pcie_mreq_type && !w_mreq_head_ep)
                ##1 (cur_state==S_RX_DATA && r_mreq_fifo_wr_en)[*1:$]
                ##1 (s_axis_rx_tvalid && w_rx_is_eof[4] && !w_rx_is_sof[4]));

// Straddled CPLD start and HOLD end
cover property (pcie_user_rst_n ##1
                (cur_state==S_RX_IDLE_SOF && s_axis_rx_tvalid && w_rx_is_sof[4] &&
                 w_rx_is_sof[3] && !w_rx_is_eof[4] && w_pcie_cpld_type &&
                 !w_cpld_head_ep && (w_cpld_head_cs==0))
                ##1 (cur_state==S_RX_STRADDLED && r_cpld_fifo_wr_en)[*1:$]
                ##1 (s_axis_rx_tvalid && w_rx_is_eof[4] && w_rx_is_eof[3])
                ##1 (cur_state==S_RX_STRADDLED_HOLD));

// Tag last observed and propagated
cover property (r_cpld_tag_last ##1 r_cpld_fifo_tag_last);

// Error scenarios observed
cover property ($rose(r_pcie_mreq_err));
cover property ($rose(r_pcie_cpld_err));
cover property ($rose(r_pcie_cpld_len_err));

// pragma coverage on
// synthesis translate_on