
module Arithmetic_Logic_Unit (
    input [4:0] ctrl,
    input [15:0] data_in_A,
    input [15:0] data_in_B,
    output [15:0] data_out
);

// Internal register to store the result
reg [15:0] data_out_reg;

// Combinational logic to perform the operations
always @(*) begin
    case (ctrl)
        1: data_out_reg = data_in_A + data_in_B;
        2: data_out_reg = data_in_A - data_in_B;
        3: data_out_reg = data_in_A * data_in_B;
        4: data_out_reg = data_in_A / data_in_B;
        5: data_out_reg = data_in_A & data_in_B;
        6: data_out_reg = data_in_A | data_in_B;
        7: data_out_reg = data_in_A ^ data_in_B;
        8: data_out_reg = ~data_in_A;
        9: data_out_reg = data_in_A << data_in_B[3:0];
        10: data_out_reg = data_in_A >> data_in_B[3:0];
        11: data_out_reg = data_in_A <<< data_in_B[3:0];
        12: data_out_reg = data_in_A >>> data_in_B[3:0];
        default: data_out_reg = 16'b0; // Default to 0 for invalid operations
    endcase
end

// Output assignment
assign data_out = data_out_reg;

endmodule