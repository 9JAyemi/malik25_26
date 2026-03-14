module figuras_Gato_sva (
    input logic        video_mostrar,
    input logic [3:0]  entrada,
    input logic [9:0]  pixel_x,
    input logic [9:0]  pixel_y,
    input logic [2:0]  salida_rgb
);

    // salida_rgb outputs only 000, 001, or 111.
    check_rgb_value_domain: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (salida_rgb == 3'b000) || (salida_rgb == 3'b001) || (salida_rgb == 3'b111)
    );

    // When video_mostrar=1 and entrada=0011 in rect (150..200,100..150), output 111.
    check_video_on_rect1_white: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (video_mostrar == 1'b1) &&
        (entrada == 4'b0011) &&
        (pixel_x >= 10'd150) && (pixel_x <= 10'd200) &&
        (pixel_y >= 10'd100) && (pixel_y <= 10'd150)
        |-> (salida_rgb == 3'b111)
    );

    // When video_mostrar=1 and not in rect1 with entrada=0011, output 000.
    check_video_on_else_black: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (video_mostrar == 1'b1) &&
        !((entrada == 4'b0011) &&
          (pixel_x >= 10'd150) && (pixel_x <= 10'd200) &&
          (pixel_y >= 10'd100) && (pixel_y <= 10'd150))
        |-> (salida_rgb == 3'b000)
    );

    // When video_mostrar=0 and entrada=0100 in rect (100..200,50..150), output 001.
    check_video_off_rect2_blue: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (video_mostrar == 1'b0) &&
        (entrada == 4'b0100) &&
        (pixel_x >= 10'd100) && (pixel_x <= 10'd200) &&
        (pixel_y >= 10'd50)  && (pixel_y <= 10'd150)
        |-> (salida_rgb == 3'b001)
    );

    // When video_mostrar=0 and not in rect2 with entrada=0100, output 000.
    check_video_off_else_black: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (video_mostrar == 1'b0) &&
        !((entrada == 4'b0100) &&
          (pixel_x >= 10'd100) && (pixel_x <= 10'd200) &&
          (pixel_y >= 10'd50)  && (pixel_y <= 10'd150))
        |-> (salida_rgb == 3'b000)
    );

    // Output 111 occurs only when video_mostrar=1 with entrada=0011 in rect1.
    check_white_implies_video_on_rect1: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (salida_rgb == 3'b111)
        |-> (video_mostrar == 1'b1) &&
            (entrada == 4'b0011) &&
            (pixel_x >= 10'd150) && (pixel_x <= 10'd200) &&
            (pixel_y >= 10'd100) && (pixel_y <= 10'd150)
    );

    // Output 001 occurs only when video_mostrar=0 with entrada=0100 in rect2.
    check_blue_implies_video_off_rect2: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (salida_rgb == 3'b001)
        |-> (video_mostrar == 1'b0) &&
            (entrada == 4'b0100) &&
            (pixel_x >= 10'd100) && (pixel_x <= 10'd200) &&
            (pixel_y >= 10'd50)  && (pixel_y <= 10'd150)
    );

    // When video_mostrar=1, output is either 000 or 111.
    check_video_on_output_domain: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (video_mostrar == 1'b1) |-> (salida_rgb == 3'b000) || (salida_rgb == 3'b111)
    );

    // When video_mostrar=1, all RGB bits are equal (000 or 111).
    check_video_on_bits_equal: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (video_mostrar == 1'b1) |-> (salida_rgb[2] == salida_rgb[1]) && (salida_rgb[1] == salida_rgb[0])
    );

    // When video_mostrar=0, upper RGB bits are 0 (outputs 000 or 001).
    check_video_off_upper_bits_zero: assert property (
        @(posedge pixel_x[0]) disable iff (1'b0)
        (video_mostrar == 1'b0) |-> (salida_rgb[2] == 1'b0) && (salida_rgb[1] == 1'b0)
    );

endmodule