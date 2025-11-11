module Peripheral_clk_generator (clk, rst, d_in, cs, addr, rd, wr, d_out);

    input clk;
    input rst;
    input [15:0] d_in;
    input cs;
    input [3:0] addr;
    input rd;
    input wr;
    output reg [15:0] d_out;

    reg [5:0] s;
    reg [31:0] limit;
    reg [31:0] count;
    reg en = 0;
    wire clk_0;
    wire done;

    always @(*) begin
        case (addr)
            4'h0: begin s = (cs && wr) ? 6'b000001 : 6'b000000; end //limit
            4'h2: begin s = (cs && wr) ? 6'b000010 : 6'b000000; end //count
            4'h4: begin s = (cs && wr) ? 6'b000100 : 6'b000000; end //en
            4'h6: begin s = (cs && rd) ? 6'b001000 : 6'b000000; end //done
            4'h8: begin s = (cs && rd) ? 6'b010000 : 6'b000000; end //clk_0
            default: begin s = 6'b000000; end
        endcase
    end

    always @(negedge clk) begin
        limit = (s[0]) ? d_in : limit;
        count = (s[1]) ? d_in : count;
        en = (s[2]) ? d_in : en;
    end

    clk_generator c_g (.clk(clk), .rst(rst), .limit(limit), .count(count), .en(en), .clk_0(clk_0), .done(done));

    always @(negedge clk) begin
        case (s[5:3])
            3'b001: d_out[0] = done;
            3'b010: d_out = clk_0;
            default: d_out = 0;
        endcase
    end

endmodule

module clk_generator (clk, rst, limit, count, en, clk_0, done);

    input clk;
    input rst;
    input [31:0] limit;
    input [31:0] count;
    input en;
    output reg clk_0;
    output reg done;

    reg [31:0] cnt;

    always @(posedge clk) begin
        if (rst) begin
            cnt <= 0;
            clk_0 <= 0;
            done <= 1;
        end else begin
            if (en) begin
                if (cnt == limit) begin
                    cnt <= 0;
                    clk_0 <= ~clk_0;
                    done <= 1;
                end else begin
                    cnt <= cnt + 1;
                    done <= 0;
                end
            end else begin
                cnt <= 0;
                clk_0 <= 0;
                done <= 1;
            end
        end
    end

endmodule