module paula_audio_channel
(
  input   clk,          input clk7_en,
  input  cck,          input   reset,            input  aen,          input  dmaena,          input  [3:1] reg_address_in,    input   [15:0] data,       output  [6:0] volume,      output  [7:0] sample,      output  intreq,          input  intpen,          output  reg dmareq,        output  reg dmas,        input  strhor          );

parameter  AUDLEN = 4'h4;
parameter  AUDPER = 4'h6;
parameter  AUDVOL = 4'h8;
parameter  AUDDAT = 4'ha;

reg    [15:0] audlen;      reg    [15:0] audper;      reg    [6:0] audvol;      reg    [15:0] auddat;      reg    [15:0] datbuf;      reg    [2:0] audio_state;    reg    [2:0] audio_next;     wire  datwrite;        reg    volcntrld;        reg    pbufld1;        reg    [15:0] percnt;      reg    percount;        reg    percntrld;        wire  perfin;          reg    [15:0] lencnt;      reg    lencount;        reg    lencntrld;        wire  lenfin;          reg   AUDxDAT;        wire  AUDxON;          reg    AUDxDR;          reg    AUDxIR;          wire  AUDxIP;          reg    intreq2_set;
reg    intreq2_clr;
reg    intreq2;        reg    dmasen;          reg    penhi;          reg silence;  reg silence_d;  reg dmaena_d;


always @(posedge clk) begin
  if (clk7_en) begin
    if (reset)
      audlen[15:0] <= 16'h00_00;
    else if (aen && (reg_address_in[3:1]==AUDLEN[3:1]))
      audlen[15:0] <= data[15:0];
  end
end

always @(posedge clk) begin
  if (clk7_en) begin
    if (reset)
      audper[15:0] <= 16'h00_00;
    else if (aen && (reg_address_in[3:1]==AUDPER[3:1]))
      audper[15:0] <= data[15:0];
  end
end

always @(posedge clk) begin
  if (clk7_en) begin
    if (reset)
      audvol[6:0] <= 7'b000_0000;
    else if (aen && (reg_address_in[3:1]==AUDVOL[3:1]))
      audvol[6:0] <= data[6:0];
  end
end

assign datwrite = (aen && (reg_address_in[3:1]==AUDDAT[3:1])) ? 1'b1 : 1'b0;

always @(posedge clk) begin
  if (clk7_en) begin
    if (reset)
      auddat[15:0] <= 16'h00_00;
    else if (datwrite)
      auddat[15:0] <= data[15:0];
  end
end

always @(posedge clk) begin
  if (clk7_en) begin
    if (datwrite)
      AUDxDAT <= 1'b1;
    else if (cck)
      AUDxDAT <= 1'b0;
  end
end

assign  AUDxON = dmaena;  assign  AUDxIP = intpen;  assign intreq = AUDxIR;    always @(posedge clk) begin
  if (clk7_en) begin
    if (percntrld && cck)percnt[15:0] <= audper[15:0];
    else if (percount && cck)percnt[15:0] <= percnt[15:0] - 16'd1;
  end
end

assign perfin = (percnt[15:0]==1 && cck) ? 1'b1 : 1'b0;

always @(posedge clk) begin
  if (clk7_en) begin
    if (lencntrld && cck) begin lencnt[15:0] <= (audlen[15:0]);
      silence<=1'b0;
      if(audlen==1 || audlen==0)
         silence<=1'b1;
    end else if (lencount && cck)lencnt[15:0] <= (lencnt[15:0] - 1);
    dmaena_d<=dmaena;
    if(dmaena_d==1'b1 && dmaena==1'b0) begin
      silence_d<=1'b1; silence<=1'b1;
    end
    if(AUDxDAT && cck)  if(silence_d)
        silence_d<=1'b0;
      else
        silence<=1'b0;
  end
end

assign lenfin = (lencnt[15:0]==1 && cck) ? 1'b1 : 1'b0;


always @(posedge clk) begin
  if (clk7_en) begin
    if (reset)
      datbuf[15:0] <= 16'h00_00;
    else if (pbufld1 && cck)
      datbuf[15:0] <= auddat[15:0];
  end
end

assign sample[7:0] = silence ? 8'b0 : (penhi ? datbuf[15:8] : datbuf[7:0]);

assign volume[6:0] = audvol[6:0];


always @(posedge clk) begin
  if (clk7_en) begin
    if (reset)
    begin
      dmareq <= 1'b0;
      dmas <= 1'b0;
    end
    else if (AUDxDR && cck)
    begin
      dmareq <= 1'b1;
      dmas <= dmasen | lenfin;
    end
    else if (strhor) begin
      dmareq <= 1'b0;
      dmas <= 1'b0;
    end
  end
end

always @(posedge clk) begin
  if (clk7_en) begin
    if (cck)
      if (intreq2_set)
        intreq2 <= 1'b1;
      else if (intreq2_clr)
        intreq2 <= 1'b0;
  end
end

parameter AUDIO_STATE_0 = 3'b000;
parameter AUDIO_STATE_1 = 3'b001;
parameter AUDIO_STATE_2 = 3'b011;
parameter AUDIO_STATE_3 = 3'b010;
parameter AUDIO_STATE_4 = 3'b110;

always @(posedge clk) begin
  if (clk7_en) begin
    if (reset)
      audio_state <= AUDIO_STATE_0;
    else if (cck)
      audio_state <= audio_next;
  end
end

always @(*) begin
  case (audio_state)

    AUDIO_STATE_0: begin
      intreq2_clr = 1'b1;
      intreq2_set = 1'b0;
      lencount = 1'b0;
      penhi = 1'b0;
      percount = 1'b0;
      percntrld = 1'b1;

      if (AUDxON) begin
        audio_next = AUDIO_STATE_1;
        AUDxDR = 1'b1;
        AUDxIR = 1'b0;
        dmasen = 1'b1;
        lencntrld = 1'b1;
        pbufld1 = 1'b0;
        volcntrld = 1'b0;
      end
      else if (AUDxDAT && !AUDxON && !AUDxIP)  begin
        audio_next = AUDIO_STATE_3;
        AUDxDR = 1'b0;
        AUDxIR = 1'b1;
        dmasen = 1'b0;
        lencntrld = 1'b0;
        pbufld1 = 1'b1;
        volcntrld = 1'b1;
      end
      else
      begin
        audio_next = AUDIO_STATE_0;
        AUDxDR = 1'b0;
        AUDxIR = 1'b0;
        dmasen = 1'b0;
        lencntrld = 1'b0;
        pbufld1 = 1'b0;
        volcntrld = 1'b0;
      end
    end

    AUDIO_STATE_1: begin
      dmasen = 1'b0;
      intreq2_clr = 1'b1;
      intreq2_set = 1'b0;
      lencntrld = 1'b0;
      penhi = 1'b0;
      percount = 1'b0;

      if (AUDxON && AUDxDAT) begin
        audio_next = AUDIO_STATE_2;
        AUDxDR = 1'b1;
        AUDxIR = 1'b1;
        lencount = ~lenfin;
        pbufld1 = 1'b0;  percntrld = 1'b0;
        volcntrld = 1'b0;
      end
      else if (!AUDxON) begin
        audio_next = AUDIO_STATE_0;
        AUDxDR = 1'b0;
        AUDxIR = 1'b0;
        lencount = 1'b0;
        pbufld1 = 1'b0;
        percntrld = 1'b0;
        volcntrld = 1'b0;
      end
      else
      begin
        audio_next = AUDIO_STATE_1;
        AUDxDR = 1'b0;
        AUDxIR = 1'b0;
        lencount = 1'b0;
        pbufld1 = 1'b0;
        percntrld = 1'b0;
        volcntrld = 1'b0;
      end
    end

    AUDIO_STATE_2: begin
      dmasen = 1'b0;
      intreq2_clr = 1'b1;
      intreq2_set = 1'b0;
      lencntrld = 1'b0;
      penhi = 1'b0;
      percount = 1'b0;

      if (AUDxON && AUDxDAT) begin
        audio_next = AUDIO_STATE_3;
        AUDxDR = 1'b1;
        AUDxIR = 1'b0;
        lencount = ~lenfin;
        pbufld1 = 1'b1;  percntrld = 1'b1;
        volcntrld = 1'b1;
      end
      else if (!AUDxON) begin
        audio_next = AUDIO_STATE_0;
        AUDxDR = 1'b0;
        AUDxIR = 1'b0;
        lencount = 1'b0;
        pbufld1 = 1'b0;
        percntrld = 1'b0;
        volcntrld = 1'b0;
      end
      else
      begin
        audio_next = AUDIO_STATE_2;
        AUDxDR = 1'b0;
        AUDxIR = 1'b0;
        lencount = 1'b0;
        pbufld1 = 1'b0;
        percntrld = 1'b0;
        volcntrld = 1'b0;
      end
    end

    AUDIO_STATE_3: begin
      AUDxDR = 1'b0;
      AUDxIR = 1'b0;
      dmasen = 1'b0;
      intreq2_clr = 1'b0;
      intreq2_set = lenfin & AUDxON & AUDxDAT;
      lencount = ~lenfin & AUDxON & AUDxDAT;
      lencntrld = lenfin & AUDxON & AUDxDAT;
      pbufld1 = 1'b0;
      penhi = 1'b1;
      volcntrld = 1'b0;

      if (perfin) begin
        audio_next = AUDIO_STATE_4;
        percount = 1'b0;
        percntrld = 1'b1;
      end
      else
      begin
        audio_next = AUDIO_STATE_3;
        percount = 1'b1;
        percntrld = 1'b0;
      end
    end

    AUDIO_STATE_4: begin
      dmasen = 1'b0;
      intreq2_set = lenfin & AUDxON & AUDxDAT;
      lencount = ~lenfin & AUDxON & AUDxDAT;
      lencntrld = lenfin & AUDxON & AUDxDAT;
      penhi = 1'b0;
      volcntrld = 1'b0;

      if (perfin && (AUDxON || !AUDxIP)) begin
        audio_next = AUDIO_STATE_3;
        AUDxDR = AUDxON;
        AUDxIR = (intreq2 & AUDxON) | ~AUDxON;
        intreq2_clr = intreq2;
        pbufld1 = 1'b1;
        percount = 1'b0;
        percntrld = 1'b1;
      end
      else if (perfin && !AUDxON && AUDxIP) begin
        audio_next = AUDIO_STATE_0;
        AUDxDR = 1'b0;
        AUDxIR = 1'b0;
        intreq2_clr = 1'b0;
        pbufld1 = 1'b0;
        percount = 1'b0;
        percntrld = 1'b0;
      end
      else
      begin
        audio_next = AUDIO_STATE_4;
        AUDxDR = 1'b0;
        AUDxIR = 1'b0;
        intreq2_clr = 1'b0;
        pbufld1 = 1'b0;
        percount = 1'b1;
        percntrld = 1'b0;
      end
    end

    default:
    begin
      audio_next = AUDIO_STATE_0;
      AUDxDR = 1'b0;
      AUDxIR = 1'b0;
      dmasen = 1'b0;
      intreq2_clr = 1'b0;
      intreq2_set = 1'b0;
      lencntrld = 1'b0;
      lencount = 1'b0;
      pbufld1 = 1'b0;
      penhi = 1'b0;
      percount = 1'b0;
      percntrld = 1'b0;
      volcntrld = 1'b0;
    end

  endcase
end


endmodule

