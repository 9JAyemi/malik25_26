module shift_register #(
    parameter WIDTH = 8
) (
    input clk,
    input rst,
    input data_in,
    input shift_in,
    output reg data_out
);

    reg [WIDTH-1:0] reg_data;

    always @ (posedge clk) begin
        if (rst) begin
            reg_data <= 0;
        end else begin
            reg_data <= {reg_data[WIDTH-2:0], shift_in};
            if (data_in) begin
                reg_data <= {reg_data[WIDTH-2:0], 1'b1};
            end
        end
    end

    always @ (*) begin
        data_out <= reg_data[0];
    end

endmodule