module barrel_shift_up_down_counter (
    input clk,
    input reset,
    input select,
    input [3:0] data_in,
    input [1:0] shift,
    input shift_right,
    input shift_left,
    input rotate_right,
    input rotate_left,
    output reg [3:0] count
);

reg [3:0] shifted_data;

always @ (posedge clk) begin
    if (reset) begin
        count <= 4'b0000;
        shifted_data <= 4'b0000;
    end else begin
        if (select) begin
            count <= 4'b0000;
        end else begin
            count <= data_in;
        end
        
        case (shift)
            2'b00: shifted_data <= shift_right ? {shifted_data[2:0], shifted_data[3]} : {shifted_data[3], shifted_data[2:0]};
            2'b01: shifted_data <= shift_left ? {shifted_data[3], shifted_data[2:0], shifted_data[1]} : {shifted_data[0], shifted_data[3:1]};
            2'b10: shifted_data <= rotate_right ? {shifted_data[3], shifted_data[2:0]} : {shifted_data[2], shifted_data[3:1]};
            2'b11: shifted_data <= rotate_left ? {shifted_data[3], shifted_data[0], shifted_data[2:1]} : {shifted_data[1], shifted_data[3:0]};
        endcase
        
        count <= shifted_data;
    end
end

endmodule