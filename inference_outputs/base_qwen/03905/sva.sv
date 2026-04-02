module shift_register_sva (
    input logic clk,
    input logic [7:0] data,
    input logic [7:0] shifted_data
);
    // Shift register should update on every positive edge of the clock
    shift_update: assert property (
        @(posedge clk) $stable(data) |-> $stable(shifted_data)
    );
endmodule