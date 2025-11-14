module fifo(datain, rd, wr, rst, clk, full, empty, led_n, wei);

input [3:0] datain;
input rd, wr, rst, clk;

output [6:0] led_n;
output full, empty, wei;

reg [3:0] dataout;
reg full_in, empty_in, wei_in, div;
reg [3:0] mem [15:0];
reg [23:0] cnt;
reg [3:0] rp, wp;
reg [6:0] led_n;

assign full = full_in;
assign empty = empty_in;
assign wei = wei_in;

parameter
    reg0 = 7'b0000001,
    reg1 = 7'b1001111,
    reg2 = 7'b0010010,
    reg3 = 7'b0000110,
    reg4 = 7'b1001100,
    reg5 = 7'b0100100,
    reg6 = 7'b0100000,
    reg7 = 7'b0001101,
    reg8 = 7'b0000000,
    reg9 = 7'b0000100,
    rega = 7'b0001000,
    regb = 7'b1100000,
    regc = 7'b0110001,
    regd = 7'b1000010,
    rege = 7'b0110000,
    regf = 7'b0111000;

// memory read out
always @(posedge clk) begin
    if (~rd && ~empty_in) begin
        dataout <= mem[rp];
        case (dataout)
            4'h0: led_n <= reg0;
            4'h1: led_n <= reg1;
            4'h2: led_n <= reg2;
            4'h3: led_n <= reg3;
            4'h4: led_n <= reg4;
            4'h5: led_n <= reg5;
            4'h6: led_n <= reg6;
            4'h7: led_n <= reg7;
            4'h8: led_n <= reg8;
            4'h9: led_n <= reg9;
            4'ha: led_n <= rega;
            4'hb: led_n <= regb;
            4'hc: led_n <= regc;
            4'hd: led_n <= regd;
            4'he: led_n <= rege;
            4'hf: led_n <= regf;
            default:;
        endcase
    end
end

// memory write in
always @(posedge div) begin
    if (~wr && ~full_in) begin
        mem[wp] <= datain;
        wei_in <= 1'b1;
    end
end

// memory write pointer increment
always @(posedge div) begin
    if (!rst) begin
        wp <= 0;
    end else begin
        if (~wr && ~full_in) begin
            wp <= wp + 1'b1;
        end
    end
end

// memory read pointer increment
always @(posedge div) begin
    if (!rst) begin
        rp <= 0;
    end else begin
        if (~rd && ~empty_in) begin
            rp <= rp + 1'b1;
        end
    end
end

// Full signal generate
always @(posedge div) begin
    if (!rst) begin
        full_in <= 1'b0;
    end else begin
        if (rd && ~wr) begin
            if ((wp == rp - 1) || (rp == 4'h0 && wp == 4'hf)) begin
                full_in <= 1'b1;
            end
        end else if (full_in && ~rd) begin
            full_in <= 1'b0;
        end
    end
end

// Empty signal generate
always @(posedge div) begin
    if (!rst) begin
        empty_in <= 1'b1;
    end else begin
        if (~rd && wr) begin
            if ((rp == wp - 1) || (rp == 4'hf && wp == 4'h0)) begin
                empty_in <= 1'b1;
            end
        end else if (empty_in && ~wr) begin
            empty_in <= 1'b0;
        end
    end
end

always @(posedge clk) begin
    if (cnt == 24'b111111111111111111111111) begin
        div <= ~div;
        cnt <= 0;
    end else begin
        cnt <= cnt + 1;
    end
end

endmodule