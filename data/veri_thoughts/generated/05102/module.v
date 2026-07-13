module counter(
    input clk, rst, ctrl,
    input [7:0] max_val,
    input [7:0] min_val,
    output reg [7:0] count
);

    always @(posedge clk, posedge rst) begin
        if(rst) begin
            count <= 8'd0;
        end else begin
            if(ctrl) begin
                if(count == max_val) begin
                    count <= 8'd0;
                end else begin
                    count <= count + 8'd1;
                end
            end else begin
                if(count == min_val) begin
                    count <= max_val;
                end else begin
                    count <= count - 8'd1;
                end
            end
        end
    end

endmodule