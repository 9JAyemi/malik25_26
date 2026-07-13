module niosII_system_nios2_qsys_0_nios2_oci_dbrk (
    // inputs:
    E_st_data,
    av_ld_data_aligned_filtered,
    clk,
    d_address,
    d_read,
    d_waitrequest,
    d_write,
    debugack,
    reset_n,

    // outputs:
    cpu_d_address,
    cpu_d_read,
    cpu_d_readdata,
    cpu_d_wait,
    cpu_d_write,
    cpu_d_writedata,
    dbrk_break,
    dbrk_goto0,
    dbrk_goto1,
    dbrk_traceme,
    dbrk_traceoff,
    dbrk_traceon,
    dbrk_trigout
);

    input [31:0] E_st_data;
    input [31:0] av_ld_data_aligned_filtered;
    input clk;
    input [24:0] d_address;
    input d_read;
    input d_waitrequest;
    input d_write;
    input debugack;
    input reset_n;
    output [24:0] cpu_d_address;
    output cpu_d_read;
    output [31:0] cpu_d_readdata;
    output cpu_d_wait;
    output cpu_d_write;
    output [31:0] cpu_d_writedata;
    output dbrk_break;
    output dbrk_goto0;
    output dbrk_goto1;
    output dbrk_traceme;
    output dbrk_traceoff;
    output dbrk_traceon;
    output dbrk_trigout;

    reg [31:0] cpu_d_writedata_reg;
    reg [24:0] cpu_d_address_reg;
    reg cpu_d_read_reg;
    reg [31:0] cpu_d_readdata_reg;
    reg cpu_d_wait_reg;
    reg cpu_d_write_reg;
    reg dbrk_break_reg;
    reg dbrk_goto0_reg;
    reg dbrk_goto1_reg;
    reg dbrk_traceme_reg;
    reg dbrk_traceoff_reg;
    reg dbrk_traceon_reg;
    reg dbrk_trigout_reg;

    wire [31:0] dbrk_data;
    assign dbrk_data = cpu_d_write_reg ? cpu_d_writedata_reg : cpu_d_readdata_reg;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            cpu_d_writedata_reg <= 0;
            cpu_d_address_reg <= 0;
            cpu_d_read_reg <= 0;
            cpu_d_readdata_reg <= 0;
            cpu_d_wait_reg <= 0;
            cpu_d_write_reg <= 0;
            dbrk_break_reg <= 0;
            dbrk_goto0_reg <= 0;
            dbrk_goto1_reg <= 0;
            dbrk_traceme_reg <= 0;
            dbrk_traceoff_reg <= 0;
            dbrk_traceon_reg <= 0;
            dbrk_trigout_reg <= 0;
        end else begin
            cpu_d_writedata_reg <= d_write ? E_st_data : av_ld_data_aligned_filtered;
            cpu_d_address_reg <= d_write ? d_address : 0;
            cpu_d_read_reg <= d_write ? 0 : d_read;
            cpu_d_readdata_reg <= d_read ? av_ld_data_aligned_filtered : 0;
            cpu_d_wait_reg <= d_waitrequest;
            cpu_d_write_reg <= d_write;
            dbrk_break_reg <= !debugack ? ~dbrk_break_reg : dbrk_break_reg;
            dbrk_goto0_reg <= 0;
            dbrk_goto1_reg <= 0;
            dbrk_traceme_reg <= 0;
            dbrk_traceoff_reg <= 0;
            dbrk_traceon_reg <= 0;
            dbrk_trigout_reg <= 0;
        end
    end

    assign cpu_d_writedata = cpu_d_writedata_reg;
    assign cpu_d_address = cpu_d_address_reg;
    assign cpu_d_read = cpu_d_read_reg;
    assign cpu_d_readdata = cpu_d_readdata_reg;
    assign cpu_d_wait = cpu_d_wait_reg;
    assign cpu_d_write = cpu_d_write_reg;
    assign dbrk_break = dbrk_break_reg;
    assign dbrk_goto0 = dbrk_goto0_reg;
    assign dbrk_goto1 = dbrk_goto1_reg;
    assign dbrk_traceme = dbrk_traceme_reg;
    assign dbrk_traceoff = dbrk_traceoff_reg;
    assign dbrk_traceon = dbrk_traceon_reg;
    assign dbrk_trigout = dbrk_trigout_reg;

endmodule