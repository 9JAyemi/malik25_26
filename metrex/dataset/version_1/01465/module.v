module dff_ram (
    input clk,
    input rst_n,
    input [3:0] d,
    input we,
    input [7:0] waddr,
    input re,
    input [7:0] raddr,
    output reg [3:0] q
);

    reg [3:0] ram [0:7];
    reg [2:0] read_ptr;
    reg [2:0] write_ptr;
    reg [2:0] next_write_ptr;

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            q <= 4'b0;
            read_ptr <= 3'b0;
            write_ptr <= 3'b0;
            next_write_ptr <= 3'b0;
        end else begin
            if (we) begin
                ram[waddr][3:0] <= d;
                next_write_ptr <= write_ptr + 1;
            end
            write_ptr <= next_write_ptr;
            if (re) begin
                q <= ram[raddr][3:0] ^ q;
                read_ptr <= read_ptr + 1;
            end
        end
    end

endmodule

module xor_ram (
    input clk,
    input rst_n,
    input [7:0] write_addr,
    input [3:0] write_data,
    input read_en,
    input [7:0] read_addr,
    output reg [7:0] final_output
);

    reg [3:0] dff_data;
    wire [3:0] ram_data;
    wire [7:0] read_ptr;
    wire [7:0] write_ptr;

    dff_ram dff_ram_inst (
        .clk(clk),
        .rst_n(rst_n),
        .d(dff_data),
        .we(1'b1),
        .waddr(write_addr),
        .re(read_en),
        .raddr(read_addr),
        .q(ram_data)
    );

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            final_output <= 8'b0;
        end else begin
            dff_data <= write_data;
            final_output <= {ram_data, dff_data};
        end
    end

endmodule