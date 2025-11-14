

module  elastic1632#(
    parameter DEPTH_LOG2 =  4,   parameter OFFSET =  7 )(
    input             wclk,
    input             rclk,

    input             isaligned_in,
    input       [1:0] charisk_in,
    input       [1:0] notintable_in,
    input       [1:0] disperror_in,
    input      [15:0] data_in,
 
    output            isaligned_out,
    output reg  [3:0] charisk_out,
    output reg  [3:0] notintable_out,
    output reg  [3:0] disperror_out,
    output reg [31:0] data_out,

output            full,
    output            empty

);
localparam ALIGN_PRIM = 32'h7B4A4ABC;
localparam FIFO_DEPTH = 1 << DEPTH_LOG2;
localparam CORR_OFFSET = OFFSET - 0;

reg            [15:0] data_in_r;
reg             [1:0] charisk_in_r;
reg             [1:0] notintable_in_r;
reg             [1:0] disperror_in_r;
reg                   aligned32_in_r;  reg                   msb_in_r;      reg                   inc_waddr;
reg    [DEPTH_LOG2:0] waddr;
wire [DEPTH_LOG2-1:0] waddr_minus = waddr[DEPTH_LOG2-1:0] - 1;
wire   [DEPTH_LOG2:0] raddr_w;
reg    [DEPTH_LOG2:0] raddr_r;
reg            [44:0] fifo_ram    [0: FIFO_DEPTH -1];
reg             [0:0] prealign_ram[0: FIFO_DEPTH -1];
reg  [FIFO_DEPTH-1:0] fill;
wire [FIFO_DEPTH-1:0] fill_out;
wire [FIFO_DEPTH-1:0] fill_out_more; wire [FIFO_DEPTH-1:0] fill_out_less; wire [FIFO_DEPTH-1:0] fill_1;
reg             [2:0] aligned_rclk;
reg             [1:0] dav_rclk;      reg             [1:0] dav_rclk_more; reg             [1:0] dav_rclk_less; wire                  skip_rclk;  wire                  skip_rclk2; reg             [1:0] add_rclk_r;                   
reg            [44:0] rdata_r;
wire                  align_out = rdata_r[44];
reg                   pre_align_out_r;
reg             [2:0] correct_r;
wire                  correct_stream = align_out && pre_align_out_r && !correct_r[2]; wire                  correct_first = pre_align_out_r && !align_out; wire                  correct = correct_stream || correct_first;

reg             [1:0] full_0; reg             [1:0] full_1; wire is_alignp_w = ({data_in,       data_in_r} ==       ALIGN_PRIM) &&
                   ({charisk_in,    charisk_in_r} ==    4'h1) &&
                   ({notintable_in, notintable_in_r} == 0) &&
                   ({disperror_in,  disperror_in_r} ==  0);
`ifdef SIMULATION
    wire  [DEPTH_LOG2:0] dbg_diff = waddr-raddr_r; wire                 dbg_dav1 = dav_rclk[1];   wire                 dbg_full0 = full_0[1];    wire                 dbg_full1 = full_1[1];    reg          [31:0]  dbg_di;                   always @(posedge wclk) begin
        if (msb_in_r) dbg_di<= {data_in,data_in_r};
    end
`endif


genvar ii;
generate
    for (ii = 0; ii < FIFO_DEPTH; ii = ii + 1)
    begin: gen_fill_out
        assign fill_out[ii] =            fill[(ii + CORR_OFFSET    ) & (FIFO_DEPTH - 1)] ^ ((ii + CORR_OFFSET    ) >= FIFO_DEPTH);
        assign fill_out_more[ii] =       fill[(ii + CORR_OFFSET + 1) & (FIFO_DEPTH - 1)] ^ ((ii + CORR_OFFSET + 1) >= FIFO_DEPTH);
        assign fill_out_less[ii] =       fill[(ii + CORR_OFFSET - 1) & (FIFO_DEPTH - 1)] ^ ((ii + CORR_OFFSET - 1) >= FIFO_DEPTH);
        assign fill_1[ii] =              fill[(ii + 1) & (FIFO_DEPTH - 1)] ^ ((ii + 1) >= FIFO_DEPTH);
    end
endgenerate
                   
always @(posedge wclk) begin
    data_in_r <= data_in;
    charisk_in_r <= charisk_in;
    notintable_in_r <= notintable_in;
    disperror_in_r <= disperror_in;
    
    if    (!isaligned_in) aligned32_in_r <= 0;
    else if (is_alignp_w) aligned32_in_r <= 1;
    
    if (!aligned32_in_r && !is_alignp_w) msb_in_r <= 1;
    else                                 msb_in_r <= !msb_in_r;
    
    inc_waddr <= !msb_in_r || (is_alignp_w && !aligned32_in_r);
    
    if (!aligned32_in_r)  waddr <= 0;
    else if (inc_waddr)   waddr <= waddr + 1;
    
    if (msb_in_r) fifo_ram[waddr[DEPTH_LOG2-1:0]] <= {is_alignp_w,
                                                      disperror_in,  disperror_in_r,
                                                      notintable_in, notintable_in_r,
                                                      charisk_in,    charisk_in_r,
                                                      data_in,       data_in_r};
    if (msb_in_r) prealign_ram[waddr_minus] <= is_alignp_w;
                                                      
    if (!aligned32_in_r)  fill <= 0;
    else if (msb_in_r)    fill <={fill[FIFO_DEPTH-2:0],~waddr[DEPTH_LOG2]};
    
end

localparam [DEPTH_LOG2:0] SIZED0 = 0;
    localparam [DEPTH_LOG2:0] SIZED1 = 1;
    localparam [DEPTH_LOG2:0] SIZED2 = 2;
    localparam [DEPTH_LOG2:0] SIZED3 = 3;
    assign raddr_w = aligned_rclk[1]? ( raddr_r + (add_rclk_r[0]? SIZED0 : (skip_rclk ? (skip_rclk2 ? SIZED3 : SIZED2) : SIZED1))) : SIZED0;

always @(posedge rclk) begin

    raddr_r <=         raddr_w;

    rdata_r <=         fifo_ram[raddr_w[DEPTH_LOG2-1:0]];
    
    pre_align_out_r <= prealign_ram[raddr_w[DEPTH_LOG2-1:0]];
    
    if (!aligned32_in_r) aligned_rclk <= 0;
    else                 aligned_rclk <= {aligned_rclk[1:0],fill[OFFSET-2] | aligned_rclk[0]};

    if (!aligned32_in_r) dav_rclk <= 0;
    else                 dav_rclk <= {dav_rclk[0],fill_out[raddr_r[DEPTH_LOG2-1:0]] ^ raddr_r[DEPTH_LOG2]};

    if (!aligned32_in_r) dav_rclk_more <= 0;
    else                 dav_rclk_more <= {dav_rclk_more[0],fill_out_more[raddr_r[DEPTH_LOG2-1:0]] ^ raddr_r[DEPTH_LOG2]};

    if (!aligned32_in_r) dav_rclk_less <= 0;
    else                 dav_rclk_less <= {dav_rclk_less[0],fill_out_less[raddr_r[DEPTH_LOG2-1:0]] ^ raddr_r[DEPTH_LOG2]};

    
    if (!aligned32_in_r) full_0 <= 1;
    else                 full_0 <= {full_0[0], fill[raddr_r[DEPTH_LOG2-1:0]] ^ raddr_r[DEPTH_LOG2]};

    if (!aligned32_in_r) full_1 <= 1;
    else                 full_1 <= {full_1[0], fill_1[raddr_r[DEPTH_LOG2-1:0]] ^ raddr_r[DEPTH_LOG2]};
    
    disperror_out <=  rdata_r[43:40];
    notintable_out <= rdata_r[39:36];
    charisk_out <=    rdata_r[35:32];
    data_out <=       rdata_r[31: 0];
    
if (correct || !aligned_rclk) correct_r <= ~0;
    else correct_r <= correct_r << 1;

if      (correct_first)  add_rclk_r <= {~dav_rclk_less[1], ~dav_rclk[1]};
    else if (correct_stream) add_rclk_r <= {1'b0,              ~dav_rclk[1]};
    else                     add_rclk_r <= add_rclk_r >> 1; 
    
end

assign skip_rclk =  correct &&  dav_rclk[1];
assign skip_rclk2 = correct_first &&  dav_rclk_more[1];

assign isaligned_out = aligned_rclk[2];
assign full =  aligned_rclk &&  full_1[1] && !full_0[1];
assign empty = aligned_rclk && !full_1[1] &&  full_0[1];
endmodule

