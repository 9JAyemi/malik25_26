
module video_palframe(

    input  wire        clk, // 28MHz clock


    input  wire        hpix,
    input  wire        vpix,

    input  wire        hblank,
    input  wire        vblank,

    input  wire        hsync_start,
    input  wire        vsync,

    input  wire [ 3:0] pixels,
    input  wire [ 3:0] border,

    input  wire        border_sync,
    input  wire        border_sync_ena,

    // ulaplus related
    input  wire [ 1:0] up_palsel,
    input  wire [ 2:0] up_paper,
    input  wire [ 2:0] up_ink,
    input  wire        up_pixel,

    input  wire        up_ena,
    input  wire        up_palwr,
    input  wire [ 5:0] up_paladdr,
    input  wire [ 7:0] up_paldata,

    input  wire        atm_palwr,
    input  wire [ 5:0] atm_paldata,


    output wire [ 5:0] palcolor, // just for palette readback

    output wire [ 5:0] color
);
    reg [7:0] palette_read;    

    wire [ 3:0] zxcolor;
    wire [ 5:0] up_color;
    wire [ 8:0] palette_color;

    reg [3:0] synced_border;

    reg vsync_r;
    reg [1:0] ctr_14;
    reg ctr_h;
    reg ctr_v;


    always @(posedge clk)
    if( border_sync )
        synced_border <= border;

    assign zxcolor = (hpix&vpix) ? pixels : (border_sync_ena ? synced_border : border);

    assign up_color = (hpix&vpix) ? {up_palsel,~up_pixel,up_pixel?up_ink:up_paper} : {3'd0,border[2:0]};

    assign palette_color = up_ena ? {3'b100,up_color} : {5'd0,zxcolor};


    // palette
    reg [7:0] palette [0:511]; // let quartus instantiate it as RAM

    always @(posedge clk)
    begin
        if( atm_palwr || up_palwr )
        begin : palette_write
            reg [8:0] pal_addr;
            pal_addr = atm_palwr ? { 5'd0, zxcolor } : { 3'b100, up_paladdr };

            palette[pal_addr] <= atm_palwr ? {atm_paldata[3:2],1'b0,atm_paldata[5:4],1'b0,atm_paldata[1:0]} : up_paldata;
        end

        palette_read <= palette[palette_color];
    end


    assign palcolor = {palette_read[4:3],palette_read[7:6], palette_read[1:0]};




    // make 3bit palette
    always @(posedge clk)
        vsync_r <= vsync;
    //
    wire vsync_start = vsync && !vsync_r;
    //
    initial ctr_14 = 2'b00;
    always @(posedge clk)
        ctr_14 <= ctr_14+2'b01;
    //
    initial ctr_h = 1'b0;
    always @(posedge clk) if( hsync_start )
        ctr_h <= ~ctr_h;
    //
    initial ctr_v = 1'b0;
    always @(posedge clk) if( vsync_start )
        ctr_v <= ~ctr_v;


    wire plus1 = ctr_14[1] ^ ctr_h ^ ctr_v;


    reg [1:0] red;
    reg [1:0] grn;
    reg [1:0] blu;

    always @(*)
    begin
        case(palette_read[7:5])
            3'b000 : red = 2'b00;
            3'b001 : red = 2'b01;
            3'b010 : red = 2'b11;
            3'b011 : red = 2'b10;
            3'b100 : red = 2'b00;
            3'b101 : red = 2'b10;
            3'b110 : red = 2'b11;
            3'b111 : red = 2'b01;
        endcase
    end


    always @(*)
    begin
        case(palette_read[4:2])
            3'b000 : grn = 2'b00;
            3'b001 : grn = 2'b01;
            3'b010 : grn = 2'b11;
            3'b011 : grn = 2'b10;
            3'b100 : grn = 2'b00;
            3'b101 : grn = 2'b10;
            3'b110 : grn = 2'b11;
            3'b111 : grn = 2'b01;
        endcase
    end


    always @(*)
    begin
        case(palette_read[1:0])
            3'b000 : blu = 2'b00;
            3'b001 : blu = 2'b01;
            3'b010 : blu = 2'b11;
            3'b011 : blu = 2'b10;
            3'b100 : blu = 2'b00;
            3'b101 : blu = 2'b10;
            3'b110 : blu = 2'b11;
            3'b111 : blu = 2'b01;
        endcase
    end



    assign color = (hblank | vblank) ? 6'd0 : {grn,red,blu};


endmodule
