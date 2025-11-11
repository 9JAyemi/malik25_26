

module timer
#(parameter WIDTH = 32, RANGE = 60)
(
    input clk_normal,
    input clk_change_time,
    input power,
    input enable,
    input reset,
    input add_time,
    input sub_time,
    output reg [(WIDTH-1):0] count,
    output reg sig_end
);

    wire true_clk;

    initial begin
        count <= 0;
        sig_end <= 0;
    end
    
    assign true_clk = (!power || reset || !enable && (add_time || sub_time)) ? clk_change_time : clk_normal;
    
    always @(posedge true_clk) begin
        if (power) begin
            if (reset) begin
                count <= 0;
            end else if (enable) begin
                count = (count + 1) % RANGE;
                
                if (count == 0) begin
                    sig_end = 1;
                end else begin
                    sig_end = 0;
                end
            end else if (add_time) begin
                count <= (count + 1) % RANGE;
            end else if (sub_time) begin
                if (count == 0) begin
                    count = RANGE-1;
                end else begin
                    count <= (count - 1);
                end
            end
        end else begin
            count <= 0;
            sig_end <= 0;
        end
    end
endmodule
