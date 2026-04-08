module db_qp_sva (
    input logic clk,
    input logic rst_n,
    input logic cbf_4x4_i,
    input logic cbf_u_4x4_i,
    input logic cbf_v_4x4_i,
    input logic qp_left_i,
    input logic qp_flag_o
);

    logic modified_flag;
    assign modified_flag = !(cbf_4x4_i || cbf_u_4x4_i || cbf_v_4x4_i);

    // Reset clears the registered output.
    check_reset_clears_qp_flag: assert property (
        @(posedge clk) !rst_n |-> (qp_flag_o == 1'b0)
    );

    // With no CBF activity and qp_left_i high, qp_flag_o sets on the next clock.
    check_unmodified_copies_high_left_qp: assert property (
        @(posedge clk) disable iff (!rst_n)
        (modified_flag && qp_left_i) |=> (qp_flag_o == 1'b1)
    );

    // With no CBF activity and qp_left_i low, qp_flag_o clears on the next clock.
    check_unmodified_copies_low_left_qp: assert property (
        @(posedge clk) disable iff (!rst_n)
        (modified_flag && !qp_left_i) |=> (qp_flag_o == 1'b0)
    );

    // Any CBF activity forces qp_flag_o low on the next clock.
    check_modified_block_clears_qp_flag: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!modified_flag) |=> (qp_flag_o == 1'b0)
    );

    // qp_flag_o matches the previous cycle's RTL update function.
    check_registered_update_function: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (qp_flag_o == $past(modified_flag && qp_left_i))
    );

endmodule