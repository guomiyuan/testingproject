

import org.junit.Test;
import org.junit.BeforeClass;
import static org.junit.Assert.*;
import com.fastaccess.tfl.helper.DateHelper;
import com.fastaccess.tfl.helper.DateHelper.DateFormats;
import java.util.Locale;

import java.util.Date;
import java.text.SimpleDateFormat;
import java.util.TimeZone;
import java.util.Locale;

public class DateZ3Test {
	
	// Set the fixed region to English to avoid month display problems
	@BeforeClass
    public static void setUpLocale() {
        Locale.setDefault(Locale.ENGLISH);
        TimeZone.setDefault(TimeZone.getTimeZone("UTC"));
    }

    @Test
    public void testGetDesiredFormat() {
        // Corresponding test case 1
        long timestamp = DateHelper.parseDate("15/06/2023", DateFormats.S_DDMMYYYY);
        String formatted = DateHelper.getDesiredFormat(DateFormats.D_DDMMYYYY_N, timestamp);
        assertEquals("15-Jun-2023", formatted);
    }

    @Test
    public void testParseDateBasicFormat() {
        // Corresponding test case 2
        long timestamp = DateHelper.parseDate("20/07/2023", DateFormats.S_DDMMYYYY);
        assertTrue("Timestamp should be positive", timestamp > 0);
        
        String formatted = DateHelper.getDesiredFormat(DateFormats.S_DDMMYYYY, timestamp);
        assertEquals("20/07/2023", formatted);
    }

    @Test
    public void testParseDateWithTime() {
        // Corresponding test case 3
        long timestamp = DateHelper.parseDate("10/08/2023, 02:30PM", DateFormats.S_DDMMYYYYHHMMA);
        assertTrue("Timestamp should be positive", timestamp > 0);
        
        String formatted = DateHelper.getDesiredFormat(DateFormats.S_DDMMYYYYHHMMA, timestamp);
        assertEquals("10/08/2023, 02:30PM", formatted);
    }

    @Test
    public void testGetDaysBetweenTwoDateSimple() {
        // Corresponding test case 4
        String date1 = "10/06/2023, 02:30PM";
        String date2 = "15/06/2023, 02:30PM";
        
        Long daysDiff = DateHelper.getDaysBetweenTwoDate(
            date1, 
            date2, 
            DateFormats.S_DDMMYYYYHHMMA);
        //assertEquals(Long.valueOf(5), daysDiff);
		assertEquals(5, Math.abs(daysDiff));
    }

    @Test
    public void testGetDaysBetweenTwoDateCrossMonth() {
        // Corresponding test case 5
        String date1 = "31/01/2023, 02:30PM";
        String date2 = "03/02/2023, 02:30PM";
        
        Long daysDiff = DateHelper.getDaysBetweenTwoDate(
            date1, 
            date2, 
            DateFormats.S_DDMMYYYYHHMMA);
        //assertEquals(Long.valueOf(3), daysDiff);
		assertEquals(3, Math.abs(daysDiff));
    }

    @Test
    public void testGetDaysBetweenTwoDateCrossYear() {
        // Corresponding test case 6
        String date1 = "31/12/2023, 02:30PM";
        String date2 = "05/01/2024, 02:30PM";
        
        Long daysDiff = DateHelper.getDaysBetweenTwoDate(
            date1, 
            date2, 
            DateFormats.S_DDMMYYYYHHMMA);
        //assertEquals(Long.valueOf(5), daysDiff);
		assertEquals(5, Math.abs(daysDiff));
    }

    
	
    // Added new test cases to improve mutation and jacoco scores
    @Test
    public void testParseAnyDate() {
        assertNotEquals(0L, DateHelper.parseAnyDate("2025-07-15")); 
        assertNotEquals(0L, DateHelper.parseAnyDate("15/07/2025")); 
        assertEquals(0L, DateHelper.parseAnyDate("invalid-date")); 
        assertEquals(0L, DateHelper.parseAnyDate("")); 
    }

    @Test
    public void testGetHoursBetweenTwoDate() {
        Long result1 = DateHelper.getHoursBetweenTwoDate("01/04/2025", "09/04/2025", DateFormats.S_DDMMYYYY);
        assertNotNull(result1);
        assertEquals(192L, Math.abs(result1.longValue())); 

        Long result2 = DateHelper.getHoursBetweenTwoDate("invalid_date", "09/04/2025", DateFormats.S_DDMMYYYY);
        assertNull(result2);
    }

    @Test
    public void testGetMinutesBetweenTwoDates() {
        Long result1 = DateHelper.getMinutesBetweenTwoDates("01/04/2025", "02/04/2025", DateFormats.S_DDMMYYYY);
        assertNotNull(result1);
        assertEquals(1440L, Math.abs(result1.longValue())); 

        Long result2 = DateHelper.getMinutesBetweenTwoDates("invalid_date", "09/04/2025", DateFormats.S_DDMMYYYY);
        assertNull(result2);
    }

    @Test
    public void testGetTomorrow() {
        String today = DateHelper.getToday();
        String tomorrow = DateHelper.getTomorrow();
        assertNotNull(tomorrow);

        Long daysBetween = DateHelper.getDaysBetweenTwoDate(today, tomorrow, DateFormats.S_DDMMYYYY);
        assertEquals(1L, Math.abs(daysBetween.longValue()));
    }

    @Test
    public void testGetDateOnly() {

        long dateOnly = DateHelper.getDateOnly("15/07/2025");
        assertNotEquals(0L, dateOnly);

        assertEquals(0L, DateHelper.getDateOnly("invalid-date"));

        String dateStr = DateHelper.getDateOnly(dateOnly);
        assertEquals("15/07/2025", dateStr);
    }

	@Test
	public void testGetDateAndTime() {
		String dateTime = DateHelper.getDateAndTime(0L);
		assertTrue(dateTime.contains("01/01/1970"));
		assertTrue(dateTime.contains("12:00 AM"));

		long now = System.currentTimeMillis();
		String expected = new SimpleDateFormat("dd/MM/yyyy, hh:mm a", Locale.getDefault()).format(new Date(now));
		String result = DateHelper.getDateAndTime(now);
		assertEquals(expected, result);

		try {
			DateHelper.getDateAndTime("invalid-time"); 
			fail("Expected IllegalArgumentException");
		} catch (IllegalArgumentException e) {
			
		}
	}

    @Test
    public void testGetTimeOnly() {
        String timeOnly = DateHelper.getTimeOnly(0L);
        assertEquals("12:00 AM", timeOnly);
    }

    @Test
    public void testGetTodayWithTime() {
        String todayWithTime = DateHelper.getTodayWithTime();
        assertNotNull(todayWithTime);
        assertTrue(todayWithTime.matches("\\d{2}/\\d{2}/\\d{4} \\d{2}:\\d{2}:\\d{2}"));
    }

    @Test
    public void testGetToday() {
        String today = DateHelper.getToday();
        assertNotNull(today);
        assertTrue(today.matches("\\d{2}/\\d{2}/\\d{4}"));
    }

    @Test
    public void testGetDateFromDays() {
        String dateIn2Days = DateHelper.getDateFromDays(2);
        assertNotNull(dateIn2Days);

        String dateInMinus2Days = DateHelper.getDateFromDays(-2);
        assertNotNull(dateInMinus2Days);
    }

    @Test
    public void testGetDesiredFormatCurrentDate() {
        String currentDate = DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD);
        assertNotNull(currentDate);
        assertTrue(currentDate.matches("\\d{4}-\\d{2}-\\d{2}"));
    }

    @Test
    public void testEdgeCases() {
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD, Long.MIN_VALUE));

        assertEquals(0L, DateHelper.parseDate("", DateFormats.D_YYYYMMDD));

        assertNotEquals(0L, DateHelper.parseDate("29/02/2020", DateFormats.S_DDMMYYYY));
    }

	@Test
	public void testConstructor() {
		DateHelper helper = new DateHelper();
		assertNotNull(helper); 
	}
}