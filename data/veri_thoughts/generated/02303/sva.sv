module ll_axis_bridge_sva #(
    parameter DATA_WIDTH = 8
)(
    input  logic                   clk,
    input  logic                   rst,

    input  logic [DATA_WIDTH-1:0]  ll_data_in,
    input  logic                   ll_sof_in_n,
    input  logic                   ll_eof_in_n,
    input  logic                   ll_src_rdy_in_n,
    input  logic                   ll_dst_rdy_out_n,

    input  logic [DATA_WIDTH-1:0]  axis_tdata,
    input  logic                   axis_tvalid,
    input  logic                   axis_tready,
    input  logic                   axis_tlast
);
    // Clock: clk; Reset: rst (active-high)
    // Logic: purely combinational bridge with direct/inverted mappings
    // Mappings: axis_tdata=ll_data_in; axis_tvalid=~ll_src_rdy_in_n; axis_tlast=~ll_eof_in_n; ll_dst_rdy_out_n=~axis_tready

    // axis_tdata directly reflects ll_data_in each cycle.
    map_data_equiv: assert property (
        @(posedge clk) disable iff (rst) (axis_tdata == ll_data_in)
    );

    // axis_tvalid is the inverse of ll_src_rdy_in_n each cycle.
    map_valid_inversion: assert property (
        @(posedge clk) disable iff (rst) (axis_tvalid == ~ll_src_rdy_in_n)
    );

    // axis_tlast is the inverse of ll_eof_in_n each cycle.
    map_last_inversion: assert property (
        @(posedge clk) disable iff (rst) (axis_tlast == ~ll_eof_in_n)
    );

    // ll_dst_rdy_out_n is the inverse of axis_tready each cycle.
    map_ready_inversion: assert property (
        @(posedge clk) disable iff (rst) (ll_dst_rdy_out_n == ~axis_tready)
    );

    // A rise on ll_src_rdy_in_n causes a fall on axis_tvalid.
    src_rdy_rise_valid_fall: assert property (
        @(posedge clk) disable iff (rst) $rose(ll_src_rdy_in_n) |-> $fell(axis_tvalid)
    );

    // A fall on ll_src_rdy_in_n causes a rise on axis_tvalid.
    src_rdy_fall_valid_rise: assert property (
        @(posedge clk) disable iff (rst) $fell(ll_src_rdy_in_n) |-> $rose(axis_tvalid)
    );

    // A rise on ll_eof_in_n causes a fall on axis_tlast.
    eof_rise_last_fall: assert property (
        @(posedge clk) disable iff (rst) $rose(ll_eof_in_n) |-> $fell(axis_tlast)
    );

    // A fall on ll_eof_in_n causes a rise on axis_tlast.
    eof_fall_last_rise: assert property (
        @(posedge clk) disable iff (rst) $fell(ll_eof_in_n) |-> $rose(axis_tlast)
    );

    // A rise on axis_tready causes a fall on ll_dst_rdy_out_n.
    tready_rise_ll_dst_fall: assert property (
        @(posedge clk) disable iff (rst) $rose(axis_tready) |-> $fell(ll_dst_rdy_out_n)
    );

    // A fall on axis_tready causes a rise on ll_dst_rdy_out_n.
    tready_fall_ll_dst_rise: assert property (
        @(posedge clk) disable iff (rst) $fell(axis_tready) |-> $rose(ll_dst_rdy_out_n)
    );

endmodule