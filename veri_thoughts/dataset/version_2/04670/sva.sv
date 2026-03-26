module mux4to1_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] select,
    input logic data_out
);

    // select 00 routes data_in[0] to data_out.
    check_select_00_routes_bit0: assert property (
        @(posedge clk) (select === 2'b00) |-> (data_out === data_in[0])
    );

    // select 01 routes data_in[1] to data_out.
    check_select_01_routes_bit1: assert property (
        @(posedge clk) (select === 2'b01) |-> (data_out === data_in[1])
    );

    // select 10 routes data_in[2] to data_out.
    check_select_10_routes_bit2: assert property (
        @(posedge clk) (select === 2'b10) |-> (data_out === data_in[2])
    );

    // select 11 routes data_in[3] to data_out.
    check_select_11_routes_bit3: assert property (
        @(posedge clk) (select === 2'b11) |-> (data_out === data_in[3])
    );

    // With stable select and selected input, data_out stays unchanged.
    check_stable_selected_path_keeps_output_stable: assert property (
        @(posedge clk)
        (($past(select) === select) &&
         (((select === 2'b00) && (data_in[0] === $past(data_in[0]))) ||
          ((select === 2'b01) && (data_in[1] === $past(data_in[1]))) ||
          ((select === 2'b10) && (data_in[2] === $past(data_in[2]))) ||
          ((select === 2'b11) && (data_in[3] === $past(data_in[3])))))
        |-> (data_out === $past(data_out))
    );

endmodule