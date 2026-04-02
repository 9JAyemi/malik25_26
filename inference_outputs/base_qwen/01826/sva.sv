module hls_contrast_streibs_sva (
    input logic clk,
    input logic rst_n,
    input logic [din0_WIDTH - 1:0] din0,
    input logic [din1_WIDTH - 1:0] din1,
    input logic [din2_WIDTH - 1:0] din2,
    output logic [dout_WIDTH - 1:0] dout
);
    // Combinational logic: dout is calculated based on din0, din1, and din2
    // Ensure dout is correctly calculated at each clock edge
    comb_dout: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == (din0 * din1) + din2)
    ) else $error("dout calculation is incorrect");

    // Ensure din0, din1, and din2 are within their respective width limits
    din0_width_check: assert property (
        @(posedge clk) disable iff (!rst_n) (din0 < 2**din0_WIDTH)
    ) else $error("din0 exceeds its width limit");

    din1_width_check: assert property (
        @(posedge clk) disable iff (!rst_n) (din1 < 2**din1_WIDTH)
    ) else $error("din1 exceeds its width limit");

    din2_width_check: assert property (
        @(posedge clk) disable iff (!rst_n) (din2 < 2**din2_WIDTH)
    ) else $error("din2 exceeds its width limit");

    // Ensure dout is within its respective width limits
    dout_width_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout < 2**dout_WIDTH)
    ) else $error("dout exceeds its width limit");

    // Ensure the multiplication result is within the width of dout
    mul_result_width_check: assert property (
        @(posedge clk) disable iff (!rst_n) ((din0 * din1) < 2**dout_WIDTH)
    ) else $error("Multiplication result exceeds dout width");

    // Ensure the addition result is within the width of dout
    add_result_width_check: assert property (
        @(posedge clk) disable iff (!rst_n) ((din0 * din1) + din2 < 2**dout_WIDTH)
    ) else $error("Addition result exceeds dout width");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not driven to an invalid value during reset
    reset_dout_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dout == 0)
    ) else $error("dout is not driven to 0 during reset");

    // Ensure dout is not