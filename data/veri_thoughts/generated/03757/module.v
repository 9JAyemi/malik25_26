
module binary_counter (
    input clk,
    input reset,
    input count_en,
    input [31:0] max_count,
    input [31:0] load_val,
    input load,
    input count_dir,
    output reg [31:0] count_out
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        count_out <= 32'b0;
    end
    else if (load) begin
        count_out <= load_val;
    end
    else if (count_en) begin
        if (count_dir) begin
            if (count_out == max_count) begin
                count_out <= 32'b0;
            end
            else begin
                count_out <= count_out + 1;
            end
        end
        else begin
            if (count_out == 0) begin
                count_out <= max_count;
            end
            else begin
                count_out <= count_out - 1;
            end
        end
    end
end

endmodule