

module sha512_w_mem(
                    input wire            clk,
                    input wire            reset_n,

                    input wire [1023 : 0] block,

                    input wire            init,
                    input wire            next,
                    output wire [63 : 0]  w
                   );


  reg [63 : 0] w_mem [0 : 15];
  reg [63 : 0] w_mem00_new;
  reg [63 : 0] w_mem01_new;
  reg [63 : 0] w_mem02_new;
  reg [63 : 0] w_mem03_new;
  reg [63 : 0] w_mem04_new;
  reg [63 : 0] w_mem05_new;
  reg [63 : 0] w_mem06_new;
  reg [63 : 0] w_mem07_new;
  reg [63 : 0] w_mem08_new;
  reg [63 : 0] w_mem09_new;
  reg [63 : 0] w_mem10_new;
  reg [63 : 0] w_mem11_new;
  reg [63 : 0] w_mem12_new;
  reg [63 : 0] w_mem13_new;
  reg [63 : 0] w_mem14_new;
  reg [63 : 0] w_mem15_new;
  reg          w_mem_we;

  reg [6 : 0] w_ctr_reg;
  reg [6 : 0] w_ctr_new;
  reg         w_ctr_we;


  reg [63 : 0] w_tmp;
  reg [63 : 0] w_new;


  assign w = w_tmp;


  always @ (posedge clk or negedge reset_n)
    begin : reg_update
      integer i;

      if (!reset_n)
        begin
          for (i = 0; i < 16; i = i + 1)
            w_mem[i] <= 64'h0;

          w_ctr_reg <= 7'h0;
        end
      else
        begin
          if (w_mem_we)
            begin
              w_mem[00] <= w_mem00_new;
              w_mem[01] <= w_mem01_new;
              w_mem[02] <= w_mem02_new;
              w_mem[03] <= w_mem03_new;
              w_mem[04] <= w_mem04_new;
              w_mem[05] <= w_mem05_new;
              w_mem[06] <= w_mem06_new;
              w_mem[07] <= w_mem07_new;
              w_mem[08] <= w_mem08_new;
              w_mem[09] <= w_mem09_new;
              w_mem[10] <= w_mem10_new;
              w_mem[11] <= w_mem11_new;
              w_mem[12] <= w_mem12_new;
              w_mem[13] <= w_mem13_new;
              w_mem[14] <= w_mem14_new;
              w_mem[15] <= w_mem15_new;
            end

          if (w_ctr_we)
              w_ctr_reg <= w_ctr_new;
        end
    end always @*
    begin : select_w
      if (w_ctr_reg < 16)
        w_tmp = w_mem[w_ctr_reg[3 : 0]];
      else
        w_tmp = w_new;
    end always @*
    begin : w_mem_update_logic
      reg [63 : 0] w_0;
      reg [63 : 0] w_1;
      reg [63 : 0] w_9;
      reg [63 : 0] w_14;
      reg [63 : 0] d0;
      reg [63 : 0] d1;

      w_mem00_new = 64'h0;
      w_mem01_new = 64'h0;
      w_mem02_new = 64'h0;
      w_mem03_new = 64'h0;
      w_mem04_new = 64'h0;
      w_mem05_new = 64'h0;
      w_mem06_new = 64'h0;
      w_mem07_new = 64'h0;
      w_mem08_new = 64'h0;
      w_mem09_new = 64'h0;
      w_mem10_new = 64'h0;
      w_mem11_new = 64'h0;
      w_mem12_new = 64'h0;
      w_mem13_new = 64'h0;
      w_mem14_new = 64'h0;
      w_mem15_new = 64'h0;
      w_mem_we    = 0;

      w_0  = w_mem[0];
      w_1  = w_mem[1];
      w_9  = w_mem[9];
      w_14 = w_mem[14];

      d0 = {w_1[0],     w_1[63 : 1]} ^ {w_1[7 : 0], w_1[63 : 8]} ^ {7'b0000000, w_1[63 : 7]};  d1 = {w_14[18 : 0], w_14[63 : 19]} ^ {w_14[60 : 0], w_14[63 : 61]} ^ {6'b000000,    w_14[63 : 6]};   w_new = w_0 + d0 + w_9 + d1;

      if (init)
        begin
          w_mem00_new = block[1023 : 960];
          w_mem01_new = block[959  : 896];
          w_mem02_new = block[895  : 832];
          w_mem03_new = block[831  : 768];
          w_mem04_new = block[767  : 704];
          w_mem05_new = block[703  : 640];
          w_mem06_new = block[639  : 576];
          w_mem07_new = block[575  : 512];
          w_mem08_new = block[511  : 448];
          w_mem09_new = block[447  : 384];
          w_mem10_new = block[383  : 320];
          w_mem11_new = block[319  : 256];
          w_mem12_new = block[255  : 192];
          w_mem13_new = block[191  : 128];
          w_mem14_new = block[127  :  64];
          w_mem15_new = block[63   :   0];
          w_mem_we    = 1;
        end

      if (next && (w_ctr_reg > 15))
        begin
          w_mem00_new = w_mem[01];
          w_mem01_new = w_mem[02];
          w_mem02_new = w_mem[03];
          w_mem03_new = w_mem[04];
          w_mem04_new = w_mem[05];
          w_mem05_new = w_mem[06];
          w_mem06_new = w_mem[07];
          w_mem07_new = w_mem[08];
          w_mem08_new = w_mem[09];
          w_mem09_new = w_mem[10];
          w_mem10_new = w_mem[11];
          w_mem11_new = w_mem[12];
          w_mem12_new = w_mem[13];
          w_mem13_new = w_mem[14];
          w_mem14_new = w_mem[15];
          w_mem15_new = w_new;
          w_mem_we    = 1;
        end
    end always @*
    begin : w_ctr
      w_ctr_new = 7'h0;
      w_ctr_we  = 1'h0;

      if (init)
        begin
          w_ctr_new = 7'h00;
          w_ctr_we  = 1'h1;
        end

      if (next)
        begin
          w_ctr_new = w_ctr_reg + 7'h01;
          w_ctr_we  = 1'h1;
        end
    end endmodule 