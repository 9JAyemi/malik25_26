module up_down_counter (
    input up_down,
    input clear,
    input load,
    input [3:0] data_in,
    input clk,
    output reg [3:0] count_out
);

    always @(posedge clk or negedge clear) begin
        if (clear == 0) begin
            count_out <= 4'b0;
        end else if (load == 1) begin
            count_out <= data_in;
        end else if (up_down == 1) begin
            count_out <= count_out + 4'b1;
        end else begin
            count_out <= count_out - 4'b1;
        end
    end

endmodule