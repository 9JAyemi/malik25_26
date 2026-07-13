module control_unit_sva (
    input logic [1:0] ctrl,
    input logic [3:0] data_in,
    input logic load,
    input logic clk,
    input logic [3:0] data_out,
    input logic valid,
    input logic [3:0] reg_data
);
    // During load, outputs hold their previous values.
    hold_outputs_during_load: assert property (
        @(posedge clk) ($past(1'b1) && load) |=> (data_out == $past(data_out)) && (valid == $past(valid))
    );

    // When load is asserted, reg_data captures data_in on the next cycle.
    load_updates_reg_data: assert property (
        @(posedge clk) load |=> (reg_data == $past(data_in))
    );

    // When load is deasserted, reg_data holds its value.
    hold_reg_data_when_not_load: assert property (
        @(posedge clk) !load |=> (reg_data == $past(reg_data))
    );

    // When !load and ctrl==00, next data_out equals reg_data and valid is 1.
    compute_passthrough_reg_data: assert property (
        @(posedge clk) (!load && (ctrl == 2'b00)) |=> ((data_out == $past(reg_data)) && (valid == 1'b1))
    );

    // When !load and ctrl==01, next data_out equals bitwise ~reg_data and valid is 1.
    compute_invert_reg_data: assert property (
        @(posedge clk) (!load && (ctrl == 2'b01)) |=> ((data_out == ~$past(reg_data)) && (valid == 1'b1))
    );

    // When !load and ctrl==10, next data_out equals data_in and valid is 1.
    compute_passthrough_data_in: assert property (
        @(posedge clk) (!load && (ctrl == 2'b10)) |=> ((data_out == $past(data_in)) && (valid == 1'b1))
    );

    // When !load and ctrl==11, next data_out equals bitwise ~data_in and valid is 1.
    compute_invert_data_in: assert property (
        @(posedge clk) (!load && (ctrl == 2'b11)) |=> ((data_out == ~$past(data_in)) && (valid == 1'b1))
    );

    // Any cycle with !load drives valid high on the next cycle.
    valid_high_on_operation: assert property (
        @(posedge clk) !load |=> (valid == 1'b1)
    );

    // load followed by ctrl==00 yields data_out equal to the loaded reg value.
    load_then_ctrl00_uses_loaded_data: assert property (
        @(posedge clk) (load ##1 (!load && (ctrl == 2'b00))) |=> (data_out == $past(data_in, 2)) && (valid == 1'b1)
    );

    // load followed by ctrl==01 yields data_out equal to ~loaded reg value.
    load_then_ctrl01_uses_inverted_loaded_data: assert property (
        @(posedge clk) (load ##1 (!load && (ctrl == 2'b01))) |=> (data_out == ~$past(data_in, 2)) && (valid == 1'b1)
    );

    // load followed by ctrl==10 yields data_out equal to next-cycle data_in.
    load_then_ctrl10_uses_next_data_in: assert property (
        @(posedge clk) (load ##1 (!load && (ctrl == 2'b10))) |=> (data_out == $past(data_in, 1)) && (valid == 1'b1)
    );

    // load followed by ctrl==11 yields data_out equal to ~next-cycle data_in.
    load_then_ctrl11_uses_inverted_next_data_in: assert property (
        @(posedge clk) (load ##1 (!load && (ctrl == 2'b11))) |=> (data_out == ~$past(data_in, 1)) && (valid == 1'b1)
    );
endmodule