// try playing with axi4
//
// we will start with just adding in the minimum wires we need,
// and then go from there
// we will start with simple single word read/writes

// this will be a memory controller, with an AXI4 interface
// it's thus an axi slave

`default_nettype none
module mem #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 32,
    parameter MEM_SIZE_BYTES = 4096
)(
    input axi_aclk,
    input axi_aresetn,

    // read address channel
    input [ADDR_WIDTH - 1:0] axi_araddr,
    input axi_arvalid,
    output reg axi_arready,

    // read data channel
    output reg [DATA_WIDTH - 1:0] axi_rdata,
    output reg axi_rlast,
    output reg axi_rvalid,
    input axi_rready,

    // write address channel
    input [ADDR_WIDTH - 1:0] axi_awaddr,
    input axi_awvalid,
    output reg axi_awready,

    // write data channel
    input [ADDR_WIDTH - 1:0] axi_wdata,
    input axi_wlast,
    input axi_wvalid,
    output reg axi_wready,

    // write response channel
    output reg axi_bresp,
    output reg axi_bvalid,
    input axi_bready
);
    typedef enum bit[1:0] {
        R_AWAIT_ADDR,
        R_SENDING_DATA,
        R_SENT_DATA
    } e_axi_read_state;

    typedef enum bit[1:0] {
        W_AWAIT_ADDR,
        W_AWAIT_DATA,
        W_SENDING_RESPONSE
    } e_axi_write_state;

    typedef enum bit[1:0] {
        AXI_BRESP_OKAY   = 2'b00,
        AXI_BRESP_EXOKAY = 2'b01,
        AXI_BRESP_SLVERR = 2'b10,
        AXI_BRESP_DECERR = 2'b11
    } e_axi_bresp;

    reg e_axi_read_state axi_read_state;
    reg e_axi_write_state axi_write_state;

    reg [ADDR_WIDTH - 1:0] write_addr;
    reg [DATA_WIDTH - 1:0] read_data;

    reg [DATA_WIDTH - 1:0] mem[MEM_SIZE_BYTES >> 2];

    always @(posedge axi_aclk) begin
        if(~axi_aresetn) begin
            axi_arready <= 0;
            axi_rvalid <= 0;
            axi_awready <= 0;
            axi_wready <= 0;
            axi_bvalid <= 0;
            axi_read_state <= R_AWAIT_ADDR;
            axi_write_state <= W_AWAIT_ADDR;
        end else begin

            axi_rvalid <= 0;
            axi_arready <= 0;
            axi_rlast <= 0;
            case(axi_read_state)
                R_AWAIT_ADDR: begin
                    axi_arready <= 1;
                    if(axi_arready & axi_arvalid) begin
                        $display("got axi_araddr", axi_araddr);
                        axi_read_state <= R_SENDING_DATA;
                        axi_arready <= 0;
                        axi_rvalid <= 1;
                        axi_rdata <= mem[axi_araddr];
                        read_data <= mem[axi_araddr];
                    end
                end
                R_SENDING_DATA: begin
                    axi_rdata <= read_data;
                    axi_rvalid <= 1;
                    axi_rlast <= 1;
                    if(axi_rready & axi_rvalid) begin
                        // master confirmed receipt
                        axi_rvalid <= 0;
                        axi_read_state <= R_AWAIT_ADDR;
                        axi_arready <= 1;
                    end
                end
            endcase

            axi_awready <= 0;
            axi_wready <= 0;
            case(axi_write_state)
                W_AWAIT_ADDR: begin
                    axi_awready <= 1;
                    if(axi_awready & axi_awvalid) begin
                        $display("got write address %0d", axi_awaddr);
                        write_addr <= axi_awaddr;
                        axi_write_state <= W_AWAIT_DATA;
                        axi_awready <= 0;
                        axi_wready <= 1;
                    end
                end
                W_AWAIT_DATA: begin
                    axi_wready <= 1;
                    if(axi_wready & axi_wvalid) begin
                        $display("write %0d to mem[%0d]", axi_wdata, write_addr);
                        mem[write_addr] <= axi_wdata;
                        axi_write_state <= W_SENDING_RESPONSE;
                        axi_wready <= 0;
                        axi_bresp <= AXI_BRESP_OKAY;
                        axi_bvalid <= 1;
                    end
                end
                W_SENDING_RESPONSE: begin
                    axi_bresp <= AXI_BRESP_OKAY;
                    axi_bvalid <= 1;
                    if(axi_bvalid & axi_bready) begin
                        axi_bvalid <= 0;
                        axi_write_state <= W_AWAIT_ADDR;
                        axi_awready <= 1;
                    end
                end
            endcase
        end
    end
endmodule

// this will read and write memroy, via axi4. It will be
// an axi4 master
module dut #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input                         axi_aclk,
    input                         axi_aresetn,

    // read address channel
    output reg [ADDR_WIDTH - 1:0] axi_araddr,
    output reg                    axi_arvalid,
    input                         axi_arready,

    // read data channel
    input [DATA_WIDTH - 1:0]      axi_rdata,
    input                         axi_rlast,
    input                         axi_rvalid,
    output reg                    axi_rready,

    // write address channel
    output reg [ADDR_WIDTH - 1:0] axi_awaddr,
    output reg                    axi_awvalid,
    input                         axi_awready,

    // write data channel
    output reg [ADDR_WIDTH - 1:0] axi_wdata,
    output reg                    axi_wlast,
    output reg                    axi_wvalid,
    input                         axi_wready,

    // write response channel
    input                         axi_bresp,
    input                         axi_bvalid,
    output reg                    axi_bready
);
    task write_mem([ADDR_WIDTH - 1:0] addr, [DATA_WIDTH - 1:0] data);
        axi_awaddr <= addr;
        axi_awvalid <= 1;
        assert(axi_awready);

        #10
        assert(~axi_awready);
        axi_awvalid <= 0;
        axi_wdata <= data;
        axi_wvalid <= 1;
        assert(axi_wready);

        #10
        assert(~axi_wready);
        axi_wvalid <= 0;
        axi_bready <= 1;
        assert(axi_bvalid);
        
        #10
        axi_bready <= 0;
        assert(~axi_bvalid);
    endtask

    task read_mem([ADDR_WIDTH - 1:0] addr, [DATA_WIDTH - 1:0] expected_data);
        axi_araddr <= addr;
        axi_arvalid <= 1;
        assert(axi_arready);

        #10
        assert(~axi_arready);
        axi_arvalid <= 0;

        axi_rready <= 1;
        assert(axi_rvalid);
        assert(axi_rdata == expected_data);
        $display("read %0d from mem[%0d]", axi_rdata, addr);

        #10
        assert(~axi_rvalid);
        axi_wvalid <= 0;
    endtask

    initial begin
        #30;
        $display("axi_aresetn %d", axi_aresetn);

        write_mem(22, 123);
        write_mem(44, 234);

        read_mem(22, 123);
        read_mem(44, 234);
    end
endmodule

module test_dut #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)();
    reg axi_aclk;
    reg axi_aresetn;

    // read address channel
    reg [ADDR_WIDTH - 1:0] axi_araddr;
    reg axi_arvalid;
    reg axi_arready;

    // read data channel
    reg [DATA_WIDTH - 1:0] axi_rdata;
    reg axi_rlast;
    reg axi_rvalid;
    reg axi_rready;

    // write address channel
    reg [ADDR_WIDTH - 1:0] axi_awaddr;
    reg axi_awvalid;
    reg axi_awready;

    // write data channel
    reg [DATA_WIDTH - 1:0] axi_wdata;
    reg axi_wlast;
    reg axi_wvalid;
    reg axi_wready;

    // write response channel
    reg axi_bresp;
    reg axi_bvalid;
    reg axi_bready;

    dut dut_(
        .axi_aclk(axi_aclk),
        .axi_aresetn(axi_aresetn),

        .axi_araddr(axi_araddr),
        .axi_arvalid(axi_arvalid),
        .axi_arready(axi_arready),

        .axi_rdata(axi_rdata),
        .axi_rlast(axi_rlast),
        .axi_rvalid(axi_rvalid),
        .axi_rready(axi_rready),

        .axi_awaddr(axi_awaddr),
        .axi_awvalid(axi_awvalid),
        .axi_awready(axi_awready),

        .axi_wdata(axi_wdata),
        .axi_wlast(axi_wlast),
        .axi_wvalid(axi_wvalid),
        .axi_wready(axi_wready),

        .axi_bresp(axi_bresp),
        .axi_bvalid(axi_bvalid),
        .axi_bready(axi_bready)
    );
    mem mem_(
        .axi_aclk(axi_aclk),
        .axi_aresetn(axi_aresetn),

        .axi_araddr(axi_araddr),
        .axi_arvalid(axi_arvalid),
        .axi_arready(axi_arready),

        .axi_rdata(axi_rdata),
        .axi_rlast(axi_rlast),
        .axi_rvalid(axi_rvalid),
        .axi_rready(axi_rready),

        .axi_awaddr(axi_awaddr),
        .axi_awvalid(axi_awvalid),
        .axi_awready(axi_awready),

        .axi_wdata(axi_wdata),
        .axi_wlast(axi_wlast),
        .axi_wvalid(axi_wvalid),
        .axi_wready(axi_wready),

        .axi_bresp(axi_bresp),
        .axi_bvalid(axi_bvalid),
        .axi_bready(axi_bready)
    );

    initial begin
        $display("clk initial");
        forever begin
            axi_aclk = 0;
            #5 axi_aclk = ~axi_aclk;
        end
    end

    initial begin
        $display("reset initial");
        axi_aresetn <= 0;
        #20
        axi_aresetn <= 1;
        #200 $finish;
    end
endmodule
