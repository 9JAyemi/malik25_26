module premuat_8_sva (
    input  logic               enable,
    input  logic               inverse,
    input  logic signed [27:0] i_0,
    input  logic signed [27:0] i_1,
    input  logic signed [27:0] i_2,
    input  logic signed [27:0] i_3,
    input  logic signed [27:0] i_4,
    input  logic signed [27:0] i_5,
    input  logic signed [27:0] i_6,
    input  logic signed [27:0] i_7,
    input  logic signed [27:0] o_0,
    input  logic signed [27:0] o_1,
    input  logic signed [27:0] o_2,
    input  logic signed [27:0] o_3,
    input  logic signed [27:0] o_4,
    input  logic signed [27:0] o_5,
    input  logic signed [27:0] o_6,
    input  logic signed [27:0] o_7
);

    ///// Combinational remap and pass-through checks (sampled on control edges) /////

    // o_0 always passes through i_0.
    check_o0_passthrough: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (o_0 == i_0)
    );

    // o_7 always passes through i_7.
    check_o7_passthrough: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (o_7 == i_7)
    );

    // When disabled, o_1 passes through i_1.
    check_disable_passthrough_o1: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (!enable) |-> (o_1 == i_1)
    );

    // When disabled, o_2 passes through i_2.
    check_disable_passthrough_o2: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (!enable) |-> (o_2 == i_2)
    );

    // When disabled, o_3 passes through i_3.
    check_disable_passthrough_o3: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (!enable) |-> (o_3 == i_3)
    );

    // When disabled, o_4 passes through i_4.
    check_disable_passthrough_o4: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (!enable) |-> (o_4 == i_4)
    );

    // When disabled, o_5 passes through i_5.
    check_disable_passthrough_o5: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (!enable) |-> (o_5 == i_5)
    );

    // When disabled, o_6 passes through i_6.
    check_disable_passthrough_o6: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (!enable) |-> (o_6 == i_6)
    );

    // When enabled and not inverted, o_1 maps to i_4.
    check_enable_map_inv0_o1: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && !inverse) |-> (o_1 == i_4)
    );

    // When enabled and not inverted, o_2 maps to i_1.
    check_enable_map_inv0_o2: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && !inverse) |-> (o_2 == i_1)
    );

    // When enabled and not inverted, o_3 maps to i_5.
    check_enable_map_inv0_o3: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && !inverse) |-> (o_3 == i_5)
    );

    // When enabled and not inverted, o_4 maps to i_2.
    check_enable_map_inv0_o4: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && !inverse) |-> (o_4 == i_2)
    );

    // When enabled and not inverted, o_5 maps to i_6.
    check_enable_map_inv0_o5: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && !inverse) |-> (o_5 == i_6)
    );

    // When enabled and not inverted, o_6 maps to i_3.
    check_enable_map_inv0_o6: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && !inverse) |-> (o_6 == i_3)
    );

    // When enabled and inverted, o_1 maps to i_2.
    check_enable_map_inv1_o1: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && inverse) |-> (o_1 == i_2)
    );

    // When enabled and inverted, o_2 maps to i_4.
    check_enable_map_inv1_o2: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && inverse) |-> (o_2 == i_4)
    );

    // When enabled and inverted, o_3 maps to i_6.
    check_enable_map_inv1_o3: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && inverse) |-> (o_3 == i_6)
    );

    // When enabled and inverted, o_4 maps to i_1.
    check_enable_map_inv1_o4: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && inverse) |-> (o_4 == i_1)
    );

    // When enabled and inverted, o_5 maps to i_3.
    check_enable_map_inv1_o5: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && inverse) |-> (o_5 == i_3)
    );

    // When enabled and inverted, o_6 maps to i_5.
    check_enable_map_inv1_o6: assert property (
        @(posedge enable or negedge enable or posedge inverse or negedge inverse) (enable && inverse) |-> (o_6 == i_5)
    );

endmodule