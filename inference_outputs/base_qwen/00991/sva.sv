module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] shift_amount,
    output logic [3:0] data_out
);
    // Sequential logic assertion for data_out
    sequential_logic: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Combinational logic assertion for shifted_data
    combinational_logic: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> (data_out == shifted_data)
    ) else $error("data_out does not match shifted_data");

    // Check for valid shift_amount values
    valid_shift_amount: assert property (
        @(posedge clk) $stable(shift_amount) |-> (shift_amount inside {[0:2]})
    ) else $error("shift_amount contains invalid value");

    // Check for stable data_in and shift_amount before data_out changes
    stable_before_change: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> (data_out == shifted_data)
    ) else $error("data_out changes before data_in and shift_amount are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_2: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_3: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_4: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_5: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_6: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_7: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_8: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_9: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");

    // Check for stable data_out after shift_amount and data_in are stable
    stable_after_change_10: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(shift_amount) |-> $stable(data_out)
    ) else $error("data_out is not stable after shift_amount and data_in are stable");
endmodule