module power_management_sva (
    input logic kill_sw,
    input logic [2:0] sel,
    input logic error,
    input logic ack,
    input logic data,
    input logic start,
    input logic clk,
    input logic [9:0] wait_cnt,
    input logic [3:0] overvolt_grace_cnt,
    input logic [15:0] undervolt_grace_cnt,
    input logic error_reg
);

    // Start low initializes the full state.
    check_start_low_resets_state: assert property (
        @(posedge clk)
        !start |=> (
            kill_sw == 1'b0 &&
            sel == 3'b111 &&
            wait_cnt == 10'd0 &&
            error_reg == 1'b0 &&
            error == 1'b0 &&
            overvolt_grace_cnt == 4'd10 &&
            undervolt_grace_cnt == 16'd50000
        )
    );

    // Start high drives the kill switch on the next cycle.
    check_start_high_sets_kill_sw: assert property (
        @(posedge clk)
        start |=> (kill_sw == 1'b1)
    );

    // Wait counter increments while no error is latched.
    check_wait_cnt_increments_when_clear: assert property (
        @(posedge clk) disable iff (!start)
        !error_reg |=> (wait_cnt == $past(wait_cnt) + 10'd1)
    );

    // Wait counter holds when an error is latched.
    check_wait_cnt_holds_when_error: assert property (
        @(posedge clk) disable iff (!start)
        error_reg |=> (wait_cnt == $past(wait_cnt))
    );

    // Select wraps from 6 back to 0 on a scan step.
    check_sel_wraps_from_six: assert property (
        @(posedge clk) disable iff (!start)
        (!error_reg && (wait_cnt == 10'd0) && (sel == 3'd6)) |=> (sel == 3'd0)
    );

    // Select increments on other scan steps.
    check_sel_advances_on_scan_step: assert property (
        @(posedge clk) disable iff (!start)
        (!error_reg && (wait_cnt == 10'd0) && (sel != 3'd6)) |=> (sel == $past(sel) + 3'd1)
    );

    // Overvoltage grace decrements on a scan step while nonzero.
    check_overvolt_grace_decrements: assert property (
        @(posedge clk) disable iff (!start)
        (!error_reg && (wait_cnt == 10'd0) && (overvolt_grace_cnt != 4'd0))
        |=> (overvolt_grace_cnt == $past(overvolt_grace_cnt) - 4'd1)
    );

    // Undervoltage grace decrements on a scan step while nonzero.
    check_undervolt_grace_decrements: assert property (
        @(posedge clk) disable iff (!start)
        (!error_reg && (wait_cnt == 10'd0) && (undervolt_grace_cnt != 16'd0))
        |=> (undervolt_grace_cnt == $past(undervolt_grace_cnt) - 16'd1)
    );

    // Ack clears error when no new fault condition is present.
    check_ack_clears_error_without_new_fault: assert property (
        @(posedge clk) disable iff (!start)
        (ack &&
         !(&wait_cnt && !(&sel) &&
           (((data == 1'b0) && (sel[0] == 1'b0) && (undervolt_grace_cnt == 16'd0)) ||
            ((data == 1'b1) && (sel[0] == 1'b1) && (overvolt_grace_cnt == 4'd0)))))
        |=> (!error_reg && !error)
    );

    // An eligible undervoltage match sets error.
    check_undervolt_fault_sets_error: assert property (
        @(posedge clk) disable iff (!start)
        (&wait_cnt && !(&sel) &&
         (data == 1'b0) && (sel[0] == 1'b0) && (undervolt_grace_cnt == 16'd0))
        |=> (error_reg == 1'b1 && error == 1'b1)
    );

    // An eligible overvoltage match sets error.
    check_overvolt_fault_sets_error: assert property (
        @(posedge clk) disable iff (!start)
        (&wait_cnt && !(&sel) &&
         (data == 1'b1) && (sel[0] == 1'b1) && (overvolt_grace_cnt == 4'd0))
        |=> (error_reg == 1'b1 && error == 1'b1)
    );

endmodule