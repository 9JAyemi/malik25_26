module wireless_communication_block_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic [1:0] ctrl,
    input logic [7:0] data_out
);

// ctrl=00 routes data_in to data_out.
    check_ctrl_00_routes_input: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (data_out == data_in)
    );

// ctrl=01 routes data_in to data_out.
    check_ctrl_01_routes_input: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (data_out == data_in)
    );

// ctrl=10 routes data_in to data_out.
    check_ctrl_10_routes_input: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (data_out == data_in)
    );

// ctrl=11 drives data_out to zero.
    check_ctrl_11_zeroes_output: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (data_out == 8'h00)
    );

// data_out matches the selected input path.
    check_output_matches_selected_input: assert property (
        @(posedge clk)
        1'b1 |-> (data_out == ((ctrl == 2'b00) ? data_in :
                               (ctrl == 2'b01) ? data_in :
                               (ctrl == 2'b10) ? data_in :
                                                  8'h00))
    );

endmodule
