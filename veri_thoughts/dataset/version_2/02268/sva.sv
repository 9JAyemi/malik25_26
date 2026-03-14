module prcfg_dac_sva(

  input logic             clk,

  input logic [31:0]      control,
  input logic [31:0]      status,

  input logic             src_dac_enable,
  input logic [15:0]      src_dac_data,
  input logic             src_dac_valid,

  input logic             dst_dac_enable,
  input logic [15:0]      dst_dac_data,
  input logic             dst_dac_valid
);

    ///// Constant status /////
    // status is hardwired to 32'h000000A0.
    check_status_constant_value: assert property (
        @(posedge clk) status == 32'h000000A0
    );

    // status remains stable over time.
    check_status_stable_over_time: assert property (
        @(posedge clk) disable iff ($initstate) status == $past(status)
    );

    ///// Registered pass-throughs /////
    // src_dac_enable is the registered copy of dst_dac_enable.
    check_src_enable_registered_from_dst_enable: assert property (
        @(posedge clk) disable iff ($initstate) src_dac_enable == $past(dst_dac_enable)
    );

    // src_dac_valid is the registered copy of dst_dac_valid.
    check_src_valid_registered_from_dst_valid: assert property (
        @(posedge clk) disable iff ($initstate) src_dac_valid == $past(dst_dac_valid)
    );

    // dst_dac_data is the registered copy of src_dac_data.
    check_dst_data_registered_from_src_data: assert property (
        @(posedge clk) disable iff ($initstate) dst_dac_data == $past(src_dac_data)
    );

    ///// Stability propagation /////
    // If dst_dac_enable was stable over the last two cycles, src_dac_enable is stable this cycle.
    check_src_enable_stable_when_dst_enable_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(dst_dac_enable) == $past(dst_dac_enable,2)) |-> (src_dac_enable == $past(src_dac_enable))
    );

    // If dst_dac_valid was stable over the last two cycles, src_dac_valid is stable this cycle.
    check_src_valid_stable_when_dst_valid_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(dst_dac_valid) == $past(dst_dac_valid,2)) |-> (src_dac_valid == $past(src_dac_valid))
    );

    // If src_dac_data was stable over the last two cycles, dst_dac_data is stable this cycle.
    check_dst_data_stable_when_src_data_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(src_dac_data) == $past(src_dac_data,2)) |-> (dst_dac_data == $past(dst_dac_data))
    );

endmodule