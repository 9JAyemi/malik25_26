module top_module (
    input clk,
    input areset,
    input load,
    input up_down,
    input select,
    output reg [4:0] counter4,
    output reg [2:0] counter3,
    output reg [5:0] sum
);

reg [4:0] counter4_next;
reg [2:0] counter3_next;

always @(posedge clk or negedge areset) begin
    if (areset == 0) begin
        counter4 <= 0;
        counter3 <= 0;
    end else begin
        if (load) begin
            if (select) begin
                counter4 <= counter4_next;
            end else begin
                counter3 <= counter3_next;
            end
        end else begin
            if (up_down) begin
                if (select) begin
                    if (counter4 == 15) begin
                        counter4_next <= 0;
                    end else begin
                        counter4_next <= counter4 + 1;
                    end
                end else begin
                    if (counter3 == 7) begin
                        counter3_next <= 0;
                    end else begin
                        counter3_next <= counter3 + 1;
                    end
                end
            end else begin
                if (select) begin
                    if (counter4 == 0) begin
                        counter4_next <= 15;
                    end else begin
                        counter4_next <= counter4 - 1;
                    end
                end else begin
                    if (counter3 == 0) begin
                        counter3_next <= 7;
                    end else begin
                        counter3_next <= counter3 - 1;
                    end
                end
            end
        end
    end
end

always @(counter4 or counter3) begin
    sum = counter4 + counter3;
end

endmodule